use iteraide::{CollectVec, IntersperseIterator, PositionsIterator, SortedUnstableIterator};
use regardless::{regardless, Error, Result};
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

#[derive(Debug, PartialEq, PartialOrd, Eq, Hash)]
pub enum Symbol {
    Terminal(String),
    NonTerminal(String),
    Lambda,
    Eof,
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Symbol::Terminal(inner), Symbol::Terminal(other)) => inner.cmp(other),
            (Symbol::Terminal(_), Symbol::NonTerminal(_)) => std::cmp::Ordering::Greater,
            (Symbol::Terminal(_), Symbol::Lambda) => std::cmp::Ordering::Greater,
            (Symbol::Terminal(_), Symbol::Eof) => std::cmp::Ordering::Greater,
            (Symbol::NonTerminal(_), Symbol::Terminal(_)) => std::cmp::Ordering::Less,
            (Symbol::NonTerminal(inner), Symbol::NonTerminal(other)) => inner.cmp(other),
            (Symbol::NonTerminal(_), Symbol::Lambda) => std::cmp::Ordering::Greater,
            (Symbol::NonTerminal(_), Symbol::Eof) => std::cmp::Ordering::Greater,
            (Symbol::Lambda, Symbol::Terminal(_)) => std::cmp::Ordering::Less,
            (Symbol::Lambda, Symbol::NonTerminal(_)) => std::cmp::Ordering::Less,
            (Symbol::Lambda, Symbol::Lambda) => std::cmp::Ordering::Equal,
            (Symbol::Lambda, Symbol::Eof) => std::cmp::Ordering::Greater,
            (Symbol::Eof, Symbol::Terminal(_)) => std::cmp::Ordering::Less,
            (Symbol::Eof, Symbol::NonTerminal(_)) => std::cmp::Ordering::Less,
            (Symbol::Eof, Symbol::Lambda) => std::cmp::Ordering::Less,
            (Symbol::Eof, Symbol::Eof) => std::cmp::Ordering::Equal,
        }
    }
}

impl FromStr for Symbol {
    type Err = Error;

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
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let symbols: Result<_> = s.split_whitespace().map(Symbol::from_str).collect();

        Ok(Self { symbols: symbols? })
    }
}

impl Display for ProductionRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.symbols
                .iter()
                .map(Symbol::to_string)
                .intersperse(" ".to_string())
                .collect::<String>()
        )
    }
}

impl FromStr for CFG {
    type Err = Error;

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
                .ok_or(regardless!("No arrow on line!"))
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

impl ProductionRule {
    pub fn symbols(&self) -> &Vec<Symbol> {
        &self.symbols
    }

    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

impl CFG {
    /// Returns a sorted list of all [`Symbol::Terminal`] symbols in the CFG.
    pub fn terminals(&self) -> Vec<&Symbol> {
        let set: BTreeSet<&Symbol> = self
            .0
            .values()
            .flatten()
            .flat_map(|pr| &pr.symbols)
            .filter(|s| matches!(*s, Symbol::Terminal(_)))
            .collect();
        set.into_iter().sorted_unstable().collect()
    }

    /// Returns a sorted list of all [`Symbol::NonTerminal`] symbols in the CFG.
    pub fn non_terminals(&self) -> Vec<&Symbol> {
        self.0.keys().sorted_unstable().collect()
    }

    /// Returns a list of all [`Symbol::Terminal`] and [`Symbol::NonTerminal`] symbols in the CFG.
    pub fn symbols(&self) -> Vec<&Symbol> {
        self.terminals()
            .into_iter()
            .chain(self.non_terminals())
            .collect()
    }

    /// Returns the CFG represented in a format easily manipulated by the caller.
    pub fn rules(&self) -> Vec<(&Symbol, &Vec<ProductionRule>)> {
        let mut res: Vec<_> = self.0.iter().collect();
        res.sort_by_key(|v| !self.start_symbol().is_ok_and(|s| v.0 == s));
        res
    }

    /// Returns the production rules of the grammar as represented.
    pub fn production_rules(&self) -> Vec<(&Symbol, &ProductionRule)> {
        let mut res: Vec<_> = Vec::new();

        for (k, v) in self.0.iter() {
            for pr in v {
                res.push((k, pr));
            }
        }
        res
    }

    /// Returns the start symbol of the CFG.
    /// This is the first [`Symbol::NonTerminal`] with a rule containing [`Symbol::Eof`].
    pub fn start_symbol(&self) -> Result<&Symbol> {
        self.0
            .iter()
            .find(|(_, v)| v.iter().any(|i| i.symbols.contains(&Symbol::Eof)))
            .map(|(k, _)| k)
            .ok_or(regardless!("No eof marker found!"))
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
                Symbol::NonTerminal(_) if s != symbol => self.first_set(s).ok(),
                Symbol::Eof => Some(BTreeSet::from([s])),
                _ => None,
            })
            .find(|set| !set.is_empty())
    }

    /// Returns the first set of a given [`Symbol::NonTerminal`] symbol.
    ///
    /// Result is `None` if the given symbol is not a [`Symbol::NonTerminal`] occurring on the LHS of the CFG.
    pub fn first_set(&self, symbol: &Symbol) -> Result<BTreeSet<&Symbol>> {
        Ok(self
            .0
            .get(symbol)
            .ok_or_else(|| regardless!("Symbol \"{}\" not a Non-Terminal of the Grammar.", symbol))?
            .iter()
            .filter_map(|pr| self.pr_first_set(pr, symbol))
            .flatten()
            .collect::<BTreeSet<&Symbol>>())
    }

    /// Returns the follow set of a given [`Symbol::NonTerminal`] symbol.
    ///
    /// Result is `None` if the given symbol is not a [`Symbol::NonTerminal`] occurring on the LHS of the CFG.
    ///
    /// ## Implementation
    ///
    /// - Finds the first set of the following symbol for each instance of the symbol in a
    ///   production rule.
    /// - If symbol is at the end of said production rule, include the follow set of the
    ///   key as well.
    /// - If the symbol at the end of the production rule is the provided [`Symbol::NonTerminal`]
    ///   (right recursive), do not recurse.
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
                            Symbol::NonTerminal(_) => self.first_set(&s).ok(),
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

    fn pr_lambda_derivable(&self, pr: &ProductionRule, symbol: &Symbol) -> bool {
        pr.symbols.iter().all(|s| {
            !matches!(s, Symbol::Terminal(_))
                && (s != symbol && self.lambda_derivable(s).is_ok_and(identity)
                    || matches!(s, Symbol::Lambda))
        })
    }

    /// Returns `Some(true)` if a given [`Symbol::NonTerminal`] symbol contains a production rule
    /// that can derive to only [`Symbol::Lambda`]\(s\).
    ///
    /// Result is `None` if the given symbol is not a [`Symbol::NonTerminal`] occurring on the LHS of the CFG.
    pub fn lambda_derivable(&self, symbol: &Symbol) -> Result<bool> {
        Ok(self
            .0
            .get(symbol)
            .ok_or_else(|| regardless!("Symbol \"{}\" not a Non-Terminal of the Grammar.", symbol))?
            .iter()
            .any(|pr| self.pr_lambda_derivable(pr, symbol)))
    }

    pub fn predict_set<'a>(
        &'a self,
        symbol: &Symbol,
        pr: &'a ProductionRule,
    ) -> Option<BTreeSet<&'a Symbol>> {
        pr.symbols
            .iter()
            .filter_map(|s| match s {
                Symbol::Terminal(_) => Some(BTreeSet::from([s])),
                Symbol::NonTerminal(_) if s != symbol => self.first_set(s).ok(),
                Symbol::Eof => Some(BTreeSet::from([s])),
                Symbol::Lambda => self.follow_set(symbol),
                _ => None,
            })
            .find(|set| !set.is_empty())
    }

    pub fn disjoint_predicts(&self, symbol: &Symbol) -> Option<bool> {
        let predicts = self
            .0
            .get(symbol)?
            .iter()
            .filter_map(|pr| self.predict_set(symbol, pr))
            .collect_vec();

        let mut not_disjoint = false;
        for (i, set) in predicts.iter().enumerate() {
            for other in predicts
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, other)| other)
            {
                not_disjoint |= !set.is_disjoint(other);
            }
        }

        Some(!not_disjoint)
    }

    pub fn parse_table(&self) -> Result<BTreeMap<&Symbol, BTreeMap<&Symbol, &ProductionRule>>> {
        let mut table: BTreeMap<&Symbol, BTreeMap<&Symbol, &ProductionRule>> = BTreeMap::new();
        for lhs in self.non_terminals() {
            if self.disjoint_predicts(lhs).is_none_or(|inner| !inner) {
                return Err(regardless!("Not all predict sets are disjoint!"));
            }

            for pr in self.0.get(lhs).ok_or(regardless!(
                "Unable to get production rules for lhs symbol!"
            ))? {
                let set = self
                    .predict_set(lhs, pr)
                    .ok_or(regardless!("Unable to get predict set!"))?;
                for terminal in set {
                    table.entry(lhs).or_default().insert(terminal, pr);
                }
            }
        }

        Ok(table)
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
