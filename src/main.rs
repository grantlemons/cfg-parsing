use std::{
    fmt::Display,
    io::{Read, Write},
    path::Path,
};

use anyhow::{Context, Result};
use cfg_parsing::*;
use clap::Parser;

mod cli_args;
use cli_args::*;

fn main() -> Result<()> {
    let args = CliArgs::parse();

    let input = read_file(&args.input)?;

    Ok(())
}

fn read_file(p: &Path) -> Result<String> {
    let mut file = std::fs::File::open(p).context("Unable to open file!")?;

    let mut res = String::new();
    file.read_to_string(&mut res)
        .context("Unable to read file contents to string!")?;

    Ok(res)
}

fn write_file(p: &Path, contents: String) -> Result<()> {
    let mut file = std::fs::File::create(p).context("Unable to create file!")?;

    file.write(contents.as_bytes())
        .context("Unable to write to file!")?;

    Ok(())
}
