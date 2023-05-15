// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::mem::size_of;
use tlvc::*;

fn fixture(s: &str) -> Vec<u8> {
    let pieces = tlvc_text::from_str(s).unwrap();
    tlvc_text::pack(&pieces)
}

fn test_fixture_a() -> Vec<u8> {
    fixture(
        r#"
        [
            ("0x1d", [])
        ]
    "#,
    )
}

#[test]
fn read_header_a() {
    let f = test_fixture_a();
    let r = TlvcReader::begin(f.as_slice()).unwrap();

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
