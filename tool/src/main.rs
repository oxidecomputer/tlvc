// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use clap::Parser;
use std::path::PathBuf;
use zerocopy::AsBytes;
use tlvc_text::Piece;

#[derive(Parser)]
struct Tool {
    #[clap(subcommand)]
    cmd: Cmd,
}

#[derive(Parser)]
enum Cmd {
    Pack {
        input: PathBuf,
        output: PathBuf,
    },
    Dump {
        input: PathBuf,
    }
}

fn main() {
    let args = Tool::from_args();
    match args.cmd {
        Cmd::Pack { input, output } => {
            let p = tlvc_text::load(std::fs::File::open(input).unwrap()).unwrap();

            let mut bytes = vec![];
            for piece in p {
                bytes.extend(pack(&piece));
            }

            std::fs::write(output, &bytes).unwrap();
        }
        Cmd::Dump { input } => {
            let bytes = std::fs::read(input).unwrap();
            let pieces = dump(tlvc::TlvcReader::begin(&bytes[..]).unwrap());
            tlvc_text::save(std::io::stdout(), &pieces).unwrap();
            println!();
        }
    }
}

fn pack(piece: &Piece) -> Vec<u8> {
    match piece {
        Piece::Bytes(b) => b.to_vec(),
        Piece::Chunk(tag, body) => {
            let mut out = vec![];

            let mut header = tlvc::ChunkHeader {
                tag: (*tag).into(),
                len: 0.into(),
                header_checksum: 0.into(),
            };

            out.extend(header.as_bytes());

            let c = tlvc::begin_body_crc();
            let mut c = c.digest();
            for p in body {
                let segment = pack(p);
                c.update(&segment);
                out.extend(segment);
            }
            let body_len = out.len() - std::mem::size_of::<tlvc::ChunkHeader>();
            let body_len = u32::try_from(body_len).unwrap();
            while out.len() & 0b11 != 0 {
                out.push(0);
            }
            out.extend(c.finalize().to_le_bytes());

            // Update the header.
            header.len.set(body_len);
            header.header_checksum.set(header.compute_checksum());

            out[..std::mem::size_of::<tlvc::ChunkHeader>()].copy_from_slice(header.as_bytes());
            out
        }
    }
}

fn dump<R>(mut src: tlvc::TlvcReader<R>) -> Vec<Piece>
    where R: tlvc::TlvcRead,
{
    let mut pieces = vec![];
    loop {
        match src.next() {
            Ok(Some(chunk)) => {
                let mut tmp = [0; 512];
                if chunk.check_body_checksum(&mut tmp).is_ok() {
                    pieces.push(Piece::Chunk(
                        tlvc_text::Tag::new(chunk.header().tag),
                        dump(chunk.read_as_chunks()),
                    ));
                } else {
                    pieces.push(Piece::Bytes(remaining_bytes(src, chunk.header().total_len_in_bytes())));
                    break;
                }
            }
            Ok(None) => break,
            Err(_) => {
                pieces.push(Piece::Bytes(remaining_bytes(src, 0)));
                break;
            },
        }
    }
    pieces
}

fn remaining_bytes<R>(src: tlvc::TlvcReader<R>, rewind: usize) -> Vec<u8>
    where R: tlvc::TlvcRead,
{
    let (src, start, end) = src.into_inner();
    let start = start as usize - rewind;
    let mut bytes = vec![0; end as usize - start];
    src.read_exact(start as u64, &mut bytes).unwrap();
    bytes
}
