use serde::{Serialize, Deserialize, de::Error};
use std::io;

pub fn load(input: impl io::Read) -> io::Result<Vec<Piece>> {
    ron::de::from_reader(input).map_err(|e| io::Error::new(io::ErrorKind::Other, e))
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
