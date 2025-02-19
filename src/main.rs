use std::{io::Read, path::Path};

use anyhow::{anyhow, Context, Result};
use cfg_parsing::*;
use clap::Parser;

mod cli_args;
use cli_args::*;

fn main() -> Result<()> {
    let args = CliArgs::parse();

    let input = read_file(&args.input)?;
    let cfg: CFG = input.parse()?;

    let non_terminal_list = cfg
        .non_terminals()
        .into_iter()
        .map(Symbol::to_string)
        .reduce(|acc, s| acc + ", " + &s)
        .ok_or(anyhow!("Unable to reduce non-terminals"))?;

    let terminal_list = cfg
        .terminals()
        .into_iter()
        .map(Symbol::to_string)
        .reduce(|acc, s| acc + ", " + &s)
        .ok_or(anyhow!("Unable to reduce terminals"))?;

    let symbol_list = cfg
        .symbols()
        .into_iter()
        .map(Symbol::to_string)
        .reduce(|acc, s| acc + ", " + &s)
        .ok_or(anyhow!("Unable to reduce symbols"))?;

    println!("Grammar Non-Terminals");
    println!("{}", non_terminal_list);
    println!("Grammar Terminals");
    println!("{}", terminal_list);
    println!("Grammar Symbols");
    println!("{}", symbol_list);

    println!("\nGrammar Rules");
    let mut rule_count = 1;
    for (lhs, rhs) in cfg.rules().into_iter().filter(|(_, r)| !r.is_empty()) {
        for rule in rhs.into_iter().filter(|r| !r.is_empty()) {
            let production = rule
                .into_iter()
                .map(Symbol::to_string)
                .reduce(|acc, s| acc + " " + &s)
                .ok_or(anyhow!("Unable to reduce symbols"))?;
            println!("({})   {} -> {}", rule_count, lhs, production);
            rule_count += 1;
        }
    }

    Ok(())
}

fn read_file(p: &Path) -> Result<String> {
    let mut file = std::fs::File::open(p).context("Unable to open file!")?;

    let mut res = String::new();
    file.read_to_string(&mut res)
        .context("Unable to read file contents to string!")?;

    Ok(res)
}
