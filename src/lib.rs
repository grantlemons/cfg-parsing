use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::{
    collections::{BTreeMap, BTreeSet},
    convert::identity,
    fmt::Display,
    str::FromStr,
};

/// LHS Non-Terminals associated with RHS [`ProductionRule`]s.
pub struct CFG(BTreeMap<Symbol, Vec<ProductionRule>>);

/// A RHS production rule of a [`CFG`].
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProductionRule {
    symbols: Vec<Symbol>,
}

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
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

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Symbol::Terminal(t) => t.clone(),
            Symbol::NonTerminal(t) => t.clone(),
            Symbol::Lambda => "lambda".to_string(),
            Symbol::Eof => "$".to_string(),
        };
        write!(f, "{}", s)
    }
}

impl FromStr for ProductionRule {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let symbols: Result<_> = s.split_whitespace().map(Symbol::from_str).collect();

        Ok(Self { symbols: symbols? })
    }
}

impl FromStr for CFG {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut res: BTreeMap<Symbol, Vec<ProductionRule>> = BTreeMap::new();
        let mut current_lhs = String::new();
        for line in s
            .lines()
            .filter(|l| !l.is_empty())
            .filter(|l| l.chars().next().is_some_and(|c| c != '#'))
        {
            let (lhs, rhs) = line
                .split_once(" -> ")
                .map(|(a, b)| (a.to_owned(), b.to_owned()))
                .ok_or(anyhow!("No arrow on line!"))
                .unwrap_or((current_lhs.clone(), line.to_owned()));
            current_lhs = lhs.clone();

            let rules: Result<Vec<_>> = rhs
                .split("| ")
                .filter(|str| !str.is_empty())
                .map(ProductionRule::from_str)
                .collect();
            for rule in rules?.into_iter().filter(|pr| !pr.symbols.is_empty()) {
                res.entry(Symbol::NonTerminal(lhs.trim().to_owned()))
                    .or_default()
                    .push(rule);
            }
        }

        Ok(Self(res))
    }
}

impl CFG {
    /// Returns a list of all [`Symbol::Terminal`] symbols in the CFG.
    pub fn terminals(&self) -> Vec<&Symbol> {
        let set: BTreeSet<&Symbol> = self
            .0
            .values()
            .flatten()
            .flat_map(|pr| &pr.symbols)
            .filter(|s| matches!(*s, Symbol::Terminal(_)))
            .collect();
        set.into_iter().collect()
    }

    /// Returns a list of all [`Symbol::NonTerminal`] symbols in the CFG.
    pub fn non_terminals(&self) -> Vec<&Symbol> {
        self.0.keys().collect()
    }

    /// Returns a list of all [`Symbol::Terminal`] and [`Symbol::NonTerminal`] symbols in the CFG.
    pub fn symbols(&self) -> Vec<&Symbol> {
        self.terminals()
            .into_iter()
            .chain(self.non_terminals())
            .collect()
    }

    /// Returns the CFG represented in a format easily manipulated by the caller.
    pub fn rules(&self) -> Vec<(&Symbol, Vec<Vec<&Symbol>>)> {
        self.0
            .iter()
            .map(|(k, v)| (k, v.iter().map(|pr| pr.symbols.iter().collect()).collect()))
            .sorted_by_key(|v| !self.start_symbol().is_some_and(|s| v.0 == s))
            .collect()
    }

    /// Returns the start symbol of the CFG.
    /// This is the first [`Symbol::NonTerminal`] with a rule containing [`Symbol::Eof`].
    pub fn start_symbol(&self) -> Option<&Symbol> {
        self.0
            .iter()
            .find(|(_, v)| v.iter().any(|i| i.symbols.contains(&Symbol::Eof)))
            .map(|(k, _)| k)
    }

    /// Returns the first set of a given production rule.
    ///
    /// Result is `None` if the production rule begins with lambda.
    fn pr_first_set<'a>(
        &'a self,
        pr: &'a ProductionRule,
        symbol: &Symbol,
    ) -> Option<BTreeSet<&'a Symbol>> {
        pr.symbols
            .iter()
            .filter_map(|s| match s {
                Symbol::Terminal(_) => Some(BTreeSet::from([s])),
                Symbol::NonTerminal(_) if s != symbol => self.first_set(s),
                Symbol::Eof => Some(BTreeSet::from([s])),
                _ => None,
            })
            .find(|set| !set.is_empty())
    }

    /// Returns the first set of a given [`Symbol::NonTerminal`] symbol.
    ///
    /// Result is `None` if the given symbol is not a [`Symbol::NonTerminal`] occurring on the LHS of the CFG.
    pub fn first_set(&self, symbol: &Symbol) -> Option<BTreeSet<&Symbol>> {
        Some(
            self.0
                .get(symbol)?
                .iter()
                .filter_map(|pr| self.pr_first_set(pr, symbol))
                .flatten()
                .collect::<BTreeSet<&Symbol>>(),
        )
    }

    /// Returns the follow set of a given [`Symbol::NonTerminal`] symbol.
    ///
    /// Result is `None` if the given symbol is not a [`Symbol::NonTerminal`] occurring on the LHS of the CFG.
    ///
    /// ## Implementation
    ///
    /// - Finds the first set of the following symbol for each instance of the symbol in a
    /// production rule.
    /// - If symbol is at the end of said production rule, include the follow set of the
    /// key as well.
    /// - If the symbol at the end of the production rule is the provided [`Symbol::NonTerminal`]
    /// (right recursive), do not recurse.
    pub fn follow_set(&self, symbol: &Symbol) -> Option<BTreeSet<&Symbol>> {
        Some(
            self.0
                .iter()
                .flat_map(|(k, v)| {
                    let mut follow_self = false;
                    let res: BTreeSet<&Symbol> = v
                        .iter()
                        .filter(|pr| pr.symbols.contains(symbol))
                        .flat_map(|pr| {
                            let follow_symbols = pr
                                .symbols
                                .iter()
                                .filter(|s| {
                                    matches!(
                                        s,
                                        Symbol::Terminal(_) | Symbol::NonTerminal(_) | Symbol::Eof
                                    )
                                })
                                .positions(|s| s == symbol)
                                .map(|pos| pr.symbols.get(pos + 1))
                                .collect::<BTreeSet<_>>();
                            if follow_symbols.contains(&None) {
                                follow_self = true;
                            }
                            follow_symbols
                        })
                        .flatten()
                        .filter_map(|s| match s {
                            Symbol::Terminal(_) => Some(BTreeSet::from([s])),
                            Symbol::NonTerminal(_) => self.first_set(s),
                            Symbol::Lambda => panic!("Lambda should not occur here!"),
                            Symbol::Eof => Some(BTreeSet::from([s])),
                        })
                        .flatten()
                        .collect();
                    if follow_self && k != symbol {
                        res.union(&self.follow_set(k).unwrap()).cloned().collect()
                    } else {
                        res
                    }
                })
                .collect(),
        )
    }

    /// Returns `Some(true)` if a given [`Symbol::NonTerminal`] symbol contains a production rule
    /// that can derive to only [`Symbol::Lambda`]\(s\).
    ///
    /// Result is `None` if the given symbol is not a [`Symbol::NonTerminal`] occurring on the LHS of the CFG.
    pub fn lambda_derivable(&self, symbol: &Symbol) -> Option<bool> {
        Some(self.0.get(symbol)?.iter().any(|pr| {
            pr.symbols.iter().all(|s| {
                !matches!(s, Symbol::Terminal(_))
                    && (s != symbol && self.lambda_derivable(s).is_some_and(identity)
                        || matches!(s, Symbol::Lambda))
            })
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

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

    #[test]
    fn test_to_lambda() {
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

        assert!(cfg
            .lambda_derivable(&Symbol::NonTerminal("A".to_string()))
            .unwrap());
        assert!(!cfg
            .lambda_derivable(&Symbol::NonTerminal("T".to_string()))
            .unwrap());
        assert!(!cfg
            .lambda_derivable(&Symbol::NonTerminal("Var".to_string()))
            .unwrap());
        assert!(!cfg
            .lambda_derivable(&Symbol::NonTerminal("E".to_string()))
            .unwrap());
    }

    #[test]
    fn test_first_set() {
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

        assert_eq!(
            cfg.first_set(&Symbol::NonTerminal("A".to_string()))
                .unwrap(),
            BTreeSet::from([
                &Symbol::Terminal("e".to_string()),
                &Symbol::Terminal("f".to_string()),
                &Symbol::Terminal("g".to_string()),
                &Symbol::Terminal("h".to_string()),
                &Symbol::Terminal("j".to_string()),
                &Symbol::Terminal("k".to_string()),
            ])
        );
        assert_eq!(
            cfg.first_set(&Symbol::NonTerminal("E".to_string()))
                .unwrap(),
            BTreeSet::from([
                &Symbol::Terminal("a".to_string()),
                &Symbol::Terminal("s".to_string()),
                &Symbol::Terminal("zero".to_string()),
            ])
            .union(
                &cfg.first_set(&Symbol::NonTerminal("A".to_string()))
                    .unwrap()
            )
            .cloned()
            .collect()
        );
    }

    #[test]
    fn test_follow_set() {
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

        assert_eq!(
            cfg.follow_set(&Symbol::NonTerminal("A".to_string()))
                .unwrap(),
            BTreeSet::from([&Symbol::Eof])
        );
        assert_eq!(
            cfg.follow_set(&Symbol::NonTerminal("Var".to_string()))
                .unwrap(),
            BTreeSet::from([&Symbol::Terminal("equal".to_string())])
                .union(
                    &cfg.follow_set(&Symbol::NonTerminal("E".to_string()))
                        .unwrap()
                )
                .cloned()
                .collect()
        );
        assert_eq!(
            cfg.follow_set(&Symbol::NonTerminal("E".to_string()))
                .unwrap(),
            cfg.follow_set(&Symbol::NonTerminal("T".to_string()))
                .unwrap()
        );
    }
}
