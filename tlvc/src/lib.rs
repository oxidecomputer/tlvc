// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Implementation of the TLV-C data structure.

#![cfg_attr(not(test), no_std)]

use core::mem::size_of;
use zerocopy::{AsBytes, FromBytes};

/// Shorthand type for little-endian `u32` used in the chunk header.
pub type U32LE = zerocopy::U32<byteorder::LittleEndian>;

/// Magic number used to compute the header checksum.
pub const HEADER_MAGIC: u32 = 0x6b32_9f69;

/// Computes the header checksum corresponding to a 4-byte tag and body length.
pub const fn header_checksum(tag: [u8; 4], len: u32) -> u32 {
    !u32::from_le_bytes(tag)
        .wrapping_mul(HEADER_MAGIC)
        .wrapping_add(len)
}

/// Layout of fields in a chunk header.
///
/// While the fields are expected to be 4-byte-aligned in the storage medium, we
/// _don't_ require them to be aligned in local memory, so this uses the
/// unaligned and explicitly little-endian version of `u32`.
#[derive(Copy, Clone, Debug, Default, AsBytes, FromBytes, zerocopy::Unaligned)]
#[repr(C)]
pub struct ChunkHeader {
    /// Identifier describing the chunk. Must be valid UTF-8.
    pub tag: [u8; 4],
    /// Number of bytes in the chunk body.
    pub len: U32LE,
    /// Checksum of the above two fields, computed using the `header_checksum`
    /// algorithm.
    pub header_checksum: U32LE,
}

impl ChunkHeader {
    /// Compute the correct checksum for the header tag and length, independent
    /// of the currently recorded checksum.
    pub fn compute_checksum(&self) -> u32 {
        header_checksum(self.tag, self.len.get())
    }

    /// Compute the length of this chunk in bytes, including the header,
    /// body, any padding, and the trailing checksum.
    pub fn total_len_in_bytes(&self) -> usize {
        size_of::<Self>() + round_up_usize(self.len.get() as usize) + 4
    }
}

/// Trait implemented by types that can serve as a source of TLV-C data. This is
/// a limited version of `std::io::Read` that can be used in a `no_std`
/// environment.
///
/// For ergonomics reasons, we require that implementations of `TlvcRead` also
/// implement `Clone`. The easiest way to do this is to implement `TlvcRead` for
/// a _reference_ to the backing store, e.g. `&MyType`.
pub trait TlvcRead: Clone {
    fn extent(&self) -> Result<u64, TlvcReadError>;
    fn read_exact(&self, offset: u64, dest: &mut [u8]) -> Result<(), TlvcReadError>;
}

/// Implementation of `TlvcRead` for a simple in-memory byte slice.
impl TlvcRead for &'_ [u8] {
    fn extent(&self) -> Result<u64, TlvcReadError> {
        Ok(u64::try_from(self.len()).unwrap())
    }

    fn read_exact(&self, offset: u64, dest: &mut [u8]) -> Result<(), TlvcReadError> {
        let offset = usize::try_from(offset).unwrap();
        let end = offset.checked_add(dest.len()).unwrap();
        dest.copy_from_slice(&self[offset..end]);
        Ok(())
    }
}

/// Implementation of `TlvcRead` for `Arc<[u8]>`. We implement this for `Arc`
/// instead of `Vec` because `Arc` can be cheaply (shallowly) cloned.
#[cfg(any(feature = "alloc", test))]
impl TlvcRead for std::sync::Arc<[u8]> {
    fn extent(&self) -> Result<u64, TlvcReadError> {
        (&**self).extent()
    }

    fn read_exact(&self, offset: u64, dest: &mut [u8]) -> Result<(), TlvcReadError> {
        (&**self).read_exact(offset, dest)
    }
}

/// Errors that can occur during the read process.
#[derive(Copy, Clone, Debug)]
pub enum TlvcReadError {
    /// A header was found with the wrong checksum.
    HeaderCorrupt {
        stored_checksum: u32,
        computed_checksum: u32,
    },
    /// A chunk body didn't match its checksum.
    BodyCorrupt {
        stored_checksum: u32,
        computed_checksum: u32,
    },
    /// A chunk would extend past the end of the medium.
    Truncated,
}

/// Pulls data from a `TlvcRead` implementation and parses it as TLV-C.
#[derive(Clone)]
pub struct TlvcReader<R> {
    source: R,
    position: u64,
    limit: u64,
}

impl<R: TlvcRead> TlvcReader<R> {
    /// Starts a reader at the beginning of `source` and covering the whole
    /// extent of the medium.
    pub fn begin(source: R) -> Result<Self, TlvcReadError> {
        let limit = source.extent()?;
        Ok(Self {
            source,
            position: 0,
            limit,
        })
    }

    /// Returns the number of bytes remaining in this reader.
    pub fn remaining(&self) -> u64 {
        self.limit - self.position
    }

    /// Destroys this reader and returns the original `source`, the byte
    /// position of the reader at the time of its destruction, and the byte
    /// offset of the reader's limit. (This will be the end of the medium for
    /// readers created directly from `source`, or a point within for
    /// sub-readers produced by `read_as_chunks`.)
    pub fn into_inner(self) -> (R, u64, u64) {
        (self.source, self.position, self.limit)
    }

    /// Attempts to parse a chunk and return a handle to it.
    ///
    /// This has three possible outcomes:
    ///
    /// 1. `Ok(Some(chunk))` - a chunk header was successfully parsed, and
    ///    describes a chunk that doesn't extend past the end of the medium.
    ///    This implies that the header checksum was validated, but does _not_
    ///    validate the body checksum, since that may require significant
    ///    amounts of I/O.
    ///
    /// 2. `Ok(None)` - this reader is at the end of its backing store.
    ///
    /// 3. `Err(e)` - data is available from the backing store, but it doesn't
    ///    validate as a chunk header, or would extend past the end.
    ///
    /// In the first case, and only the first case, this reader's position is
    /// bumped past the end of the successfully parsed chunk. This means the
    /// next call to `next` will attempt to return a different chunk.
    pub fn next(&mut self) -> Result<Option<ChunkHandle<R>>, TlvcReadError> {
        if self.position == self.limit {
            return Ok(None);
        }

        let header = self.read_header()?;
        let body_position = self.position + size_of::<ChunkHeader>() as u64;
        let body_len = round_up(u64::from(header.len.get()));
        let chunk_end = body_position + body_len + 4;

        if chunk_end > self.limit {
            return Err(TlvcReadError::Truncated);
        }
        self.position = chunk_end;

        Ok(Some(ChunkHandle {
            source: self.source.clone(),
            header,
            body_position,
        }))
    }

    /// Reads data from the backing store and attempts to validate it as a chunk
    /// header.
    ///
    /// This is an implementation factor of `next`, provided for your
    /// convenience. It checks the header _only._ It does not check that the
    /// chunk _body_ is within the backing store, or the body checksum.
    ///
    /// You almost certainly want to call `next` instead.
    pub fn read_header(&self) -> Result<ChunkHeader, TlvcReadError> {
        // Check that our invariant is maintained.
        debug_assert!(self.is_word_aligned());

        // See if this access would require us to go off the end of our region.
        let header_end = self
            .position
            .checked_add(size_of::<ChunkHeader>() as u64)
            .ok_or(TlvcReadError::Truncated)?;
        if header_end > self.limit {
            return Err(TlvcReadError::Truncated);
        }

        // Great! Read the actual bytes.
        let mut header = ChunkHeader::default();
        self.source
            .read_exact(self.position, header.as_bytes_mut())?;

        // Finally, check the header's local checksum to try and distinguish
        // this from total nonsense.
        if header.header_checksum.get() != header.compute_checksum() {
            return Err(TlvcReadError::HeaderCorrupt {
                stored_checksum: header.header_checksum.get(),
                computed_checksum: header.compute_checksum(),
            });
        }

        Ok(header)
    }

    pub fn skip_chunk(&mut self) -> Result<(), TlvcReadError> {
        let h = self.read_header()?;

        // Compute the overall size of the header, contents (rounded up for
        // alignment), and the trailing checksum (which we're not going to
        // check).
        let size = size_of::<ChunkHeader>() as u64
            + round_up(u64::from(h.len.get()))
            + size_of::<u32>() as u64;

        // Bump our new position forward as long as it doesn't cross our limit.
        // This may leave us zero-length. That's ok.
        let p = self
            .position
            .checked_add(size)
            .ok_or(TlvcReadError::Truncated)?;

        if p > self.limit {
            return Err(TlvcReadError::Truncated);
        }

        self.position = p;
        Ok(())
    }

    fn is_word_aligned(&self) -> bool {
        self.position & 0b11 == 0
    }
}

/// A validated chunk in a data source of type `R`.
///
/// Holding a `ChunkHandle` tells you that
///
/// 1. There is a chunk in the data source at some position.
/// 2. Its header checks out.
/// 3. Its body and trailing body checksum are completely contained within the
///    data source, i.e. you will not get `Truncated` errors trying to access
///    them.
///
/// You can access the chunk header with `header()` and access the body contents
/// with various other functions.
///
/// The `ChunkHandle` holds a cloned reference to the `TlvcReader`'s backing
/// data store, _not_ a reference to the `TlvcReader` itself -- so you can have
/// multiple chunk handles outstanding.
pub struct ChunkHandle<R> {
    source: R,
    header: ChunkHeader,
    body_position: u64,
}

impl<R> ChunkHandle<R> {
    /// Returns a reference to the raw chunk header.
    pub fn header(&self) -> &ChunkHeader {
        &self.header
    }

    /// Returns the length of the body in bytes.
    pub fn len(&self) -> u64 {
        u64::from(self.header.len.get())
    }

    /// Checks whether the body is empty
    pub fn is_empty(&self) -> bool {
        self.header.len.get() == 0
    }

    /// Reads bytes from the chunk body without interpreting them. Note that
    /// this does not check the body checksum.
    pub fn read_exact(&self, position: u64, dest: &mut [u8]) -> Result<(), TlvcReadError>
    where
        R: TlvcRead,
    {
        let end = position
            .checked_add(u64::try_from(dest.len()).unwrap())
            .ok_or(TlvcReadError::Truncated)?;
        if end > self.len() {
            return Err(TlvcReadError::Truncated);
        }

        self.source.read_exact(self.body_position + position, dest)
    }

    /// Produces a `TlvcReader` that can be used to interpret this chunk's body
    /// data as nested TLV-C chunks.
    ///
    /// The `TlvcReader` holds a new reference to the data source, so you can
    /// dispose of this `ChunkHandle` if desired.
    ///
    /// This _does not_ validate the body checksum. If you would like to
    /// validate the body checksum, call `check_body_checksum` before
    /// `read_as_chunks`. Note that this will (unavoidably) result in duplicate
    /// reads.
    pub fn read_as_chunks(&self) -> TlvcReader<R>
    where
        R: TlvcRead,
    {
        TlvcReader {
            source: self.source.clone(),
            position: self.body_position,
            limit: self.body_position + u64::from(self.header.len.get()),
        }
    }

    /// Reads the chunk body using the provided temporary buffer for storage,
    /// and verifies that the checksum is correct.
    ///
    /// The buffer will be filled with some portion of the data. Which portion
    /// is undefined. You should treat it as garbage after this returns.
    pub fn check_body_checksum(&self, buffer: &mut [u8]) -> Result<(), TlvcReadError>
    where
        R: TlvcRead,
    {
        let mut c = begin_body_crc();
        let end = self.body_position + self.header.len.get() as u64;
        let mut pos = self.body_position;
        while pos != end {
            let portion = usize::try_from(end - pos)
                .unwrap_or(usize::MAX)
                .min(buffer.len());
            self.source.read_exact(pos, &mut buffer[..portion])?;
            c.update(&buffer[..portion]);
            pos += u64::try_from(portion).unwrap();
        }

        let computed_checksum = c.finalize();
        let mut stored_checksum = 0u32;
        self.source
            .read_exact(round_up(end), stored_checksum.as_bytes_mut())?;

        if computed_checksum != stored_checksum {
            Err(TlvcReadError::BodyCorrupt {
                computed_checksum,
                stored_checksum,
            })
        } else {
            Ok(())
        }
    }
}

pub static CRC: crc::Crc<u32> = crc::Crc::<u32>::new(&crc::CRC_32_ISCSI);

/// Produces a `crc::Digest` that implements the polynomial used for body contents
/// checksums.
pub fn begin_body_crc() -> crc::Digest<'static, u32> {
    CRC.digest()
}

/// Utility for computing the body contents checksum for a block of data held
/// entirely in RAM.
pub fn compute_body_crc(data: &[u8]) -> u32 {
    let mut c = begin_body_crc();
    c.update(data);
    c.finalize()
}

fn round_up(x: u64) -> u64 {
    (x + 0b11) & !0b11
}

fn round_up_usize(x: usize) -> usize {
    (x + 0b11) & !0b11
}

#[cfg(test)]
mod tests {
    use super::*;

    const fn pack_tag(bytes: [u8; 4]) -> u32 {
        u32::from_le_bytes(bytes)
    }

    fn chunk_bytes(chunk: &[u32]) -> std::sync::Arc<[u8]> {
        chunk.iter().cloned().flat_map(u32::to_le_bytes).collect()
    }

    // Chunk here is written as u32s for readability, will be converted to
    // appropriate endianness for tests.
    static TEST_CHUNK_A: &[u32] = &[pack_tag(*b"0x1d"), 0, header_checksum(*b"0x1d", 0), 0];

    fn test_chunk_a() -> TlvcReader<std::sync::Arc<[u8]>> {
        TlvcReader::begin(chunk_bytes(TEST_CHUNK_A)).unwrap()
    }

    #[test]
    fn read_header_a() {
        let r = test_chunk_a();

        let h = r.read_header().expect("header should read successfully");
        assert_eq!(h.tag, *b"0x1d");
        assert_eq!(h.len.get(), 0);
        assert_eq!(h.header_checksum.get(), h.compute_checksum());

        assert_eq!(
            r.remaining(),
            (size_of::<ChunkHeader>() + size_of::<u32>()) as u64,
            "read_header should not advance cursor"
        );
    }

    #[test]
    fn next_a() {
        let mut r = test_chunk_a();
        let c = r
            .next()
            .expect("chunk should read successfully")
            .expect("chunk should not be none");

        let h = c.header();
        assert_eq!(h.tag, *b"0x1d");
        assert_eq!(h.len.get(), 0);
        assert_eq!(h.header_checksum.get(), h.compute_checksum());

        drop(c);

        assert_eq!(r.remaining(), 0, "skipping chunk should exhaust reader");
    }

    #[test]
    fn read_as_chunks_a() {
        let mut r = test_chunk_a();
        let c = r
            .next()
            .expect("chunk should read successfully")
            .expect("chunk should not be none");

        let mut r2 = c.read_as_chunks();
        assert!(r2.next().expect("empty body should read ok").is_none());
    }

    #[test]
    fn read_body_a() {
        let mut r = test_chunk_a();
        let c = r
            .next()
            .expect("chunk should read successfully")
            .expect("chunk should not be none");

        assert_eq!(c.len(), 0);

        c.read_exact(0, &mut [])
            .expect("zero-length read should succeed");

        match c.read_exact(1, &mut []) {
            Err(TlvcReadError::Truncated) => (),
            Err(e) => panic!("unexpected error: {:?}", e),
            Ok(_) => panic!("read off end of chunk succeeded"),
        }

        match c.read_exact(0, &mut [0]) {
            Err(TlvcReadError::Truncated) => (),
            Err(e) => panic!("unexpected error: {:?}", e),
            Ok(_) => panic!("read off end of chunk succeeded"),
        }

        let mut r2 = c.read_as_chunks();
        assert!(r2.next().expect("empty body should read ok").is_none());
    }

    #[test]
    fn next_checksum_a() {
        let mut r = test_chunk_a();
        let c = r
            .next()
            .expect("chunk should read successfully")
            .expect("chunk should not be none");

        let mut temp = [0; 512];
        c.check_body_checksum(&mut temp)
            .expect("body checksum should be valid");
    }

    // This chunk has a data payload that is deliberately not a multiple of 4
    // bytes in length, to test that behavior.
    //
    // This uses a hand-computed checksum.
    static TEST_CHUNK_B: &[u32] = &[
        pack_tag(*b"0x1d"),
        21,
        header_checksum(*b"0x1d", 21),
        0xDEAD_BEEF,
        0xCAFE_0B0E,
        pack_tag(*b"hell"),
        pack_tag(*b"o, w"),
        pack_tag(*b"orld"),
        pack_tag(*b"!\0\0\0"),
        0x6c1823b8,
    ];

    fn test_chunk_b() -> TlvcReader<std::sync::Arc<[u8]>> {
        TlvcReader::begin(chunk_bytes(TEST_CHUNK_B)).unwrap()
    }

    #[test]
    fn next_b() {
        let mut r = test_chunk_b();
        let c = r
            .next()
            .expect("chunk should read successfully")
            .expect("chunk should not be none");

        let h = c.header();
        assert_eq!(h.tag, *b"0x1d");

        assert_eq!(c.len(), 21);

        let mut msg = [0; 13];

        c.check_body_checksum(&mut msg)
            .expect("checksum should validate");

        c.read_exact(8, &mut msg)
            .expect("should be able to read msg");
        assert_eq!(msg, *b"hello, world!");

        drop(c);

        assert_eq!(r.remaining(), 0, "skipping chunk should exhaust reader");
    }
}
