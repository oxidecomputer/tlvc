// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use serde::{Serialize, Deserialize, de::Error};
use std::io;

pub fn load(input: impl io::Read) -> io::Result<Vec<Piece>> {
    ron::de::from_reader(input).map_err(|e| io::Error::new(io::ErrorKind::Other, e))
}

pub fn from_str(input: &str) -> ron::error::SpannedResult<Vec<Piece>> {
    ron::de::from_str(input)
}

pub fn save(output: impl io::Write, pieces: &[Piece]) -> io::Result<()> {
    ron::ser::to_writer_pretty(output, pieces, ron::ser::PrettyConfig::default()).map_err(|e| io::Error::new(io::ErrorKind::Other, e))
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum Piece {
    Chunk(Tag, Vec<Piece>),
    Bytes(Vec<u8>),
}

impl Piece {
    pub fn append_to(&self, out: &mut Vec<u8>) {
        match self {
            Self::Bytes(bytes) => out.extend(bytes),
            Self::Chunk(tag, children) => {
                out.extend(tag.0);
                let len_pos = out.len();
                let hcheck_pos = len_pos + 4;
                out.extend([0; 8]);

                let child_pos = out.len();
                for child in children {
                    child.append_to(out);
                }
                let child_len = u32::try_from(out.len() - child_pos).unwrap();

                let body_crc = tlvc::compute_body_crc(&out[out.len()..]);
                out.extend(body_crc.to_le_bytes());

                out[len_pos..len_pos + 4].copy_from_slice(&child_len.to_le_bytes());
                let hcheck = tlvc::header_checksum(tag.0, child_len);
                out[hcheck_pos..hcheck_pos + 4].copy_from_slice(&hcheck.to_le_bytes());
            }
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Tag([u8; 4]);

impl Tag {
    pub fn new(bytes: [u8; 4]) -> Self {
        // Guard against non-UTF8 data.
        if std::str::from_utf8(&bytes).is_err() {
            panic!("invalid tag: {:x?}", bytes);
        }

        Self(bytes)
    }
}

impl From<Tag> for [u8; 4] {
    fn from(t: Tag) -> Self {
        t.0
    }
}

impl Serialize for Tag {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer
    {
        let s = std::str::from_utf8(&self.0).unwrap();
        s.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Tag {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>
    {
        let s: &str = Deserialize::deserialize(deserializer)?;
        let s: &[u8; 4] = s.as_bytes().try_into()
            .map_err(|_| D::Error::custom("wrong tag length"))?;
        Ok(Tag(*s))
    }
}

pub fn pack<'a>(pieces: impl IntoIterator<Item = &'a Piece>) -> Vec<u8> {
    let mut out = vec![];

    for piece in pieces {
        piece.append_to(&mut out);
    }

    out
}
