use anyhow::{anyhow, Result};
use std::{
    collections::{BTreeMap, BTreeSet},
    str::FromStr,
};

pub struct CFG(BTreeMap<Symbol, Vec<ProductionRule>>);
pub struct ProductionRule(Vec<Symbol>);

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq)]
pub enum Symbol {
    Terminal(String),
    NonTerminal(String),
    Lambda,
    Eof,
}

impl FromStr for Symbol {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        Ok(match s.trim() {
            "lambda" => Symbol::Lambda,
            "$" => Symbol::Eof,
            nt if nt.chars().any(|c| c.is_ascii_uppercase()) => Symbol::NonTerminal(nt.to_owned()),
            t => Symbol::Terminal(t.to_owned()),
        })
    }
}

impl ToString for Symbol {
    fn to_string(&self) -> String {
        match self {
            Symbol::Terminal(t) => t.clone(),
            Symbol::NonTerminal(t) => t.clone(),
            Symbol::Lambda => "lambda".to_string(),
            Symbol::Eof => "$".to_string(),
        }
    }
}

impl FromStr for ProductionRule {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let symbols: Result<_> = s.split_whitespace().map(Symbol::from_str).collect();

        Ok(Self(symbols?))
    }
}

impl FromStr for CFG {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res: BTreeMap<Symbol, Vec<ProductionRule>> = BTreeMap::new();
        let mut current_lhs = String::new();
        for line in s.lines().filter(|l| !l.is_empty()) {
            let (lhs, rhs) = line
                .trim()
                .split_once(" -> ")
                .map(|(a, b)| (a.to_owned(), b.to_owned()))
                .ok_or(anyhow!("No arrow on line!"))
                .unwrap_or((current_lhs.clone(), line.to_owned()));
            current_lhs = lhs.clone();

            let rules: Result<Vec<_>> = rhs.split("| ").map(ProductionRule::from_str).collect();
            for rule in rules? {
                res.entry(Symbol::NonTerminal(lhs.trim().to_owned()))
                    .or_default()
                    .push(rule);
            }
        }

        Ok(Self(res))
    }
}

impl CFG {
    pub fn terminals(&self) -> Vec<&Symbol> {
        let set: BTreeSet<&Symbol> = self
            .0
            .values()
            .flatten()
            .flat_map(|pr| &pr.0)
            .filter(|s| matches!(*s, Symbol::Terminal(_)))
            .collect();
        set.into_iter().collect()
    }
    pub fn non_terminals(&self) -> Vec<&Symbol> {
        self.0.keys().collect()
    }
    pub fn symbols(&self) -> Vec<&Symbol> {
        self.terminals()
            .into_iter()
            .chain(self.non_terminals())
            .collect()
    }
    pub fn first_set(&self, _: char) -> Option<Vec<Symbol>> {
        unimplemented!()
    }
    pub fn follow_set(&self, _: char) -> Option<Vec<Symbol>> {
        unimplemented!()
    }
    pub fn lambda_derivable(&self, _: char) -> Option<bool> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Symbol, CFG};

    #[test]
    fn test_non_terminals() {
        let input = "startGoal -> A $
A -> T A
| lambda
T -> Var equal E
E -> a plus b
| s times t
E -> zero | Var
Var -> e | f | g
| h | j | k
";

        let cfg: CFG = input.parse().unwrap();
        let mut expected = [
            Symbol::NonTerminal("startGoal".to_owned()),
            Symbol::NonTerminal("A".to_owned()),
            Symbol::NonTerminal("T".to_owned()),
            Symbol::NonTerminal("E".to_owned()),
            Symbol::NonTerminal("Var".to_owned()),
        ];
        expected.sort();

        dbg!(cfg.non_terminals());
        cfg.non_terminals()
            .into_iter()
            .zip(expected)
            .for_each(|(a, b)| assert_eq!(*a, b));
    }

    #[test]
    fn test_terminals() {
        let input = "startGoal -> A $
A -> T A
| lambda
T -> Var equal E
E -> a plus b
| s times t
E -> zero | Var
Var -> e | f | g
| h | j | k
";

        let cfg: CFG = input.parse().unwrap();
        let mut expected = [
            Symbol::Terminal("equal".to_owned()),
            Symbol::Terminal("a".to_owned()),
            Symbol::Terminal("plus".to_owned()),
            Symbol::Terminal("b".to_owned()),
            Symbol::Terminal("s".to_owned()),
            Symbol::Terminal("times".to_owned()),
            Symbol::Terminal("t".to_owned()),
            Symbol::Terminal("zero".to_owned()),
            Symbol::Terminal("e".to_owned()),
            Symbol::Terminal("f".to_owned()),
            Symbol::Terminal("g".to_owned()),
            Symbol::Terminal("h".to_owned()),
            Symbol::Terminal("j".to_owned()),
            Symbol::Terminal("k".to_owned()),
        ];
        expected.sort();

        dbg!(cfg.terminals());
        cfg.terminals()
            .into_iter()
            .zip(expected)
            .for_each(|(a, b)| assert_eq!(*a, b));
    }

    #[test]
    fn test_symbols() {
        let input = "startGoal -> A $
A -> T A
| lambda
T -> Var equal E
E -> a plus b
| s times t
E -> zero | Var
Var -> e | f | g
| h | j | k
";

        let cfg: CFG = input.parse().unwrap();
        let mut expected = [
            Symbol::NonTerminal("startGoal".to_owned()),
            Symbol::NonTerminal("A".to_owned()),
            Symbol::NonTerminal("T".to_owned()),
            Symbol::NonTerminal("E".to_owned()),
            Symbol::NonTerminal("Var".to_owned()),
            Symbol::Terminal("equal".to_owned()),
            Symbol::Terminal("a".to_owned()),
            Symbol::Terminal("plus".to_owned()),
            Symbol::Terminal("b".to_owned()),
            Symbol::Terminal("s".to_owned()),
            Symbol::Terminal("times".to_owned()),
            Symbol::Terminal("t".to_owned()),
            Symbol::Terminal("zero".to_owned()),
            Symbol::Terminal("e".to_owned()),
            Symbol::Terminal("f".to_owned()),
            Symbol::Terminal("g".to_owned()),
            Symbol::Terminal("h".to_owned()),
            Symbol::Terminal("j".to_owned()),
            Symbol::Terminal("k".to_owned()),
        ];
        expected.sort();

        dbg!(cfg.symbols());
        cfg.symbols()
            .into_iter()
            .zip(expected)
            .for_each(|(a, b)| assert_eq!(*a, b));
    }
}
