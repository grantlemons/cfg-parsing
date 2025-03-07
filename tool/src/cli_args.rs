use std::path::PathBuf;

use clap::Parser;

#[derive(Parser)]
#[command(about, version)]
pub struct CliArgs {
    pub input: PathBuf,
}
