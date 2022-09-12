// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use clap::Parser;
use std::path::PathBuf;

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

            let bytes = tlvc_text::pack(&p);

            std::fs::write(output, &bytes).unwrap();
        }
        Cmd::Dump { input } => {
            let bytes = std::fs::read(input).unwrap();
            let pieces =
                tlvc_text::dump(tlvc::TlvcReader::begin(&bytes[..]).unwrap());
            tlvc_text::save(std::io::stdout(), &pieces).unwrap();
            println!();
        }
    }
}
