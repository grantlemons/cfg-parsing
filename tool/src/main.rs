use std::{collections::BTreeMap, io::Read, path::Path};

use cfg_parsing::*;
use clap::Parser;
use regardless::{regardless, Context, Error, Result};

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
        .ok_or(regardless!("Unable to reduce non-terminals"))?;

    let terminal_list = cfg
        .terminals()
        .into_iter()
        .map(Symbol::to_string)
        .reduce(|acc, s| acc + ", " + &s)
        .ok_or(regardless!("Unable to reduce terminals"))?;

    let symbol_list = cfg
        .symbols()
        .into_iter()
        .map(Symbol::to_string)
        .reduce(|acc, s| acc + ", " + &s)
        .ok_or(regardless!("Unable to reduce symbols"))?;

    println!("Grammar Non-Terminals");
    println!("{{{}}}", non_terminal_list);
    println!("Grammar Terminals");
    println!("{{{}}}", terminal_list);
    println!("Grammar Symbols");
    println!("{{{}}}", symbol_list);

    println!("\nGrammar Rules");
    let mut rule_count = 1;
    let mut rule_map: BTreeMap<(&Symbol, &ProductionRule), usize> = BTreeMap::new();
    for (lhs, rhs) in cfg.rules().into_iter().filter(|(_, r)| !r.is_empty()) {
        for rule in rhs.into_iter().filter(|r| !r.is_empty()) {
            let production = rule
                .symbols()
                .into_iter()
                .map(Symbol::to_string)
                .reduce(|acc, s| acc + " " + &s)
                .ok_or(regardless!("Unable to reduce symbols"))?;
            println!("({})   {} -> {}", rule_count, lhs, production);
            rule_map.insert((lhs, rule), rule_count);
            rule_count += 1;
        }
    }

    println!("\nStart Symbol: {}", cfg.start_symbol()?);

    for lhs in cfg.non_terminals() {
        println!(
            "\"{}\" First Set: {{{}}}",
            lhs,
            cfg.first_set(lhs)
                .context("Unable to get first set.")?
                .iter()
                .map(|s| s.to_string())
                .reduce(|acc, s| acc + ", " + &s)
                .unwrap_or_default()
        );
        println!(
            "\"{}\" Follow Set: {{{}}}",
            lhs,
            cfg.follow_set(lhs)
                .ok_or(regardless!("Unable to get follow set."))?
                .iter()
                .map(|s| s.to_string())
                .reduce(|acc, s| acc + ", " + &s)
                .unwrap_or_default()
        );
        println!(
            "\"{}\" Derives to Lambda: {}",
            lhs,
            cfg.lambda_derivable(lhs)
                .context("Unable to run derives to lambda.")?
        );
    }

    println!();
    for (symbol, rule) in cfg.production_rules() {
        println!(
            "\"{} -> {}\" Predict Set: {{{}}}",
            symbol,
            rule,
            cfg.predict_set(symbol, rule)
                .ok_or(regardless!("Unable to get predict set."))?
                .iter()
                .map(|s| s.to_string())
                .reduce(|acc, s| acc + ", " + &s)
                .unwrap_or_default()
        )
    }

    println!();
    for lhs in cfg.non_terminals() {
        println!(
            "\"{}\" Sets are disjoint?: {}",
            lhs,
            cfg.disjoint_predicts(lhs)
                .ok_or(regardless!("Could not check disjoint!"))?
        )
    }

    println!();
    let table = cfg.parse_table()?;
    for (lhs, row) in table.iter() {
        let width = table.keys().map(|k| k.to_string().len()).max().unwrap();
        print!("{:width$}", lhs);
        for terminal in cfg.terminals() {
            print!(
                "  {}",
                row.get(terminal)
                    .map(|pr| format!("{:02}", rule_map.get(&(lhs, pr)).unwrap()))
                    .unwrap_or(" --".to_owned())
            )
        }
        println!();
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
