// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use clap::Parser;
use std::path::PathBuf;
use tlvc_text::Piece;

#[derive(Parser)]
struct Tool {
    #[clap(subcommand)]
    cmd: Cmd,
}

#[derive(Parser)]
enum Cmd {
    Pack { input: PathBuf, output: PathBuf },
    Dump { input: PathBuf },
}

fn main() {
    let args = Tool::from_args();
    match args.cmd {
        Cmd::Pack { input, output } => {
            let p =
                tlvc_text::load(std::fs::File::open(input).unwrap()).unwrap();

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
    let mut out = vec![];
    piece.append_to(&mut out);
    out
}

fn dump<R>(mut src: tlvc::TlvcReader<R>) -> Vec<Piece>
where
    R: tlvc::TlvcRead,
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
                    pieces.push(Piece::Bytes(remaining_bytes(
                        src,
                        chunk.header().total_len_in_bytes(),
                    )));
                    break;
                }
            }
            Ok(None) => break,
            Err(_) => {
                pieces.push(Piece::Bytes(remaining_bytes(src, 0)));
                break;
            }
        }
    }
    pieces
}

fn remaining_bytes<R>(src: tlvc::TlvcReader<R>, rewind: usize) -> Vec<u8>
where
    R: tlvc::TlvcRead,
{
    let (src, start, end) = src.into_inner();
    let start = start as usize - rewind;
    let mut bytes = vec![0; end as usize - start];
    src.read_exact(start as u64, &mut bytes).unwrap();
    bytes
}
