use crate::ast::{CallArg, Pattern, TypedPattern};
use crate::typ::{Type, TypeConstructor, Typer};
use std::fmt;
use std::sync::Arc;

#[derive(Debug, PartialEq, Clone)]
struct Var {
    name: String,
    typ: Arc<Type>,
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
enum ClauseExpr {
    Var(Var),

    RecordConstructor {
        name: String,
        type_constructor: TypeConstructor,
        args: Vec<String>,
    },
}

impl ClauseExpr {
    fn name(&self) -> String {
        match self {
            ClauseExpr::Var(v) => v.name.clone(),

            ClauseExpr::RecordConstructor { name, .. } => name.clone(),
        }
    }
}

impl fmt::Display for ClauseExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ClauseExpr::Var(v) => write!(f, "{}", v.name),
            ClauseExpr::RecordConstructor { name, args, .. } => {
                write!(f, "{} {}", name, args.join(" "))
            }
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
enum Gdt {
    Construction {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
        t: Box<Self>,
    },

    Assignment {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
        t: Box<Self>,
    },

    Branch(Vec<Box<Self>>),

    Success,
    // Original Haskell version has ! as well
}

impl fmt::Display for Gdt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Gdt::Construction { var, expr, t } => write!(f, "let {} = {}, {}", var, expr, t),
            Gdt::Assignment { var, expr, t } => write!(f, "{} ← {}, {}", expr, var, t),
            Gdt::Branch(_branches) => write!(f, "todo"),
            Gdt::Success => write!(f, "-> x"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum FactBaseLiteral {
    // True,
    False,
    DoesNotMatch {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
    },
    Assignment {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
    },
    Construction {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
    },
}

impl fmt::Display for FactBaseLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // FactBaseLiteral::True => write!(f, "✓"),
            FactBaseLiteral::False => write!(f, "✗"),
            FactBaseLiteral::DoesNotMatch { var, expr } => write!(f, "{} ≉ {}", var, expr.name()),
            FactBaseLiteral::Assignment { var, expr } => write!(f, "{} ← {}", expr, var),
            FactBaseLiteral::Construction { var, expr } => write!(f, "let {} = {}", var, expr),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum FactBaseFormula {
    Union { lhs: Box<Self>, rhs: Box<Self> },

    Intersection { lhs: Box<Self>, rhs: Box<Self> },

    Literal(FactBaseLiteral),
}

impl fmt::Display for FactBaseFormula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FactBaseFormula::Union { lhs, rhs } => write!(f, "({} ∨ {})", lhs, rhs),
            FactBaseFormula::Intersection { lhs, rhs } => write!(f, "({} ∧ {})", lhs, rhs),
            FactBaseFormula::Literal(l) => write!(f, "{}", l),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct FactBase {
    context: Var,
    formula: Option<FactBaseFormula>,
}

impl FactBase {
    fn add_fact(&self, formula: FactBaseFormula) -> FactBase {
        match &self.formula {
            None => FactBase {
                context: self.context.clone(),
                formula: Some(formula),
            },

            Some(f) => FactBase {
                context: self.context.clone(),
                formula: Some(FactBaseFormula::Intersection {
                    lhs: Box::new(f.clone()),
                    rhs: Box::new(formula.clone()),
                }),
            },
        }
    }

    fn union(&self, other_factbase: FactBase) -> FactBase {
        match (&self.formula, &other_factbase.formula) {
            (None, None) | (Some(_), None) => self.clone(),

            (None, Some(_)) => other_factbase.clone(),

            (Some(f), Some(other_f)) => FactBase {
                context: self.context.clone(),
                formula: Some(FactBaseFormula::Union {
                    lhs: Box::new(f.clone()),
                    rhs: Box::new(other_f.clone()),
                }),
            },
        }
    }
}

impl fmt::Display for FactBase {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.formula {
            Some(formula) => write!(f, "⟨{}: Maybe A | {}⟩", self.context.name, formula),
            None => write!(f, "⟨{}: Maybe A | ø⟩", self.context.name),
        }
    }
}

pub struct CoverageChecker<'a, 'b> {
    typer: &'a Typer<'b>,
    uid: usize,
}

impl<'a, 'b> CoverageChecker<'a, 'b> {
    pub fn new(typer: &'a Typer<'b>) -> Self {
        Self { typer, uid: 0 }
    }

    pub fn construct_guard_tree(&mut self, pattern: &TypedPattern, typ: Arc<Type>) {
        let gdt = self.desugar_pattern(pattern, Some("x".to_string()), Gdt::Success);
        println!("{}", gdt);
        construct_uncovered_factbase(typ, gdt);
    }

    fn desugar_pattern(
        &mut self,
        pattern: &TypedPattern,
        var_name: Option<String>,
        mut t: Gdt,
    ) -> Gdt {
        match pattern {
            Pattern::Constructor {
                module, name, args, ..
            } => {
                let constructor = self
                    .typer
                    .get_value_constructor(module.as_ref(), name)
                    .unwrap()
                    .clone();

                let type_constructor = match &*constructor.typ {
                    Type::App { ref name, .. } => self
                        .typer
                        .get_type_constructor(module, name)
                        .unwrap()
                        .clone(),
                    Type::Fn { retrn, .. } => match &**retrn {
                        Type::App { ref name, .. } => self
                            .typer
                            .get_type_constructor(module, name)
                            .unwrap()
                            .clone(),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                let var = Box::new(Var {
                    typ: constructor.typ.clone(),
                    name: var_name.unwrap_or_else(|| self.next_variable_name(true)),
                });

                let mut vars = vec![];

                args.into_iter().rev().for_each(|arg| {
                    let CallArg { value, .. } = arg;
                    let name = self.next_variable_name(true);
                    vars.push(name.clone());

                    t = self.desugar_pattern(value, Some(name), t.clone());
                });

                Gdt::Assignment {
                    var,
                    expr: Box::new(ClauseExpr::RecordConstructor {
                        name: name.clone(),
                        type_constructor,
                        args: vars,
                    }),
                    t: Box::new(t),
                }
            }
            _ => t,
        }
    }

    fn next_variable_name(&mut self, assignment: bool) -> String {
        let alphabet_length = 26;
        let char_offset = if assignment { 121 } else { 97 }; // TODO
        let mut chars = vec![];
        let mut n;
        let mut rest = self.uid;

        loop {
            n = rest % alphabet_length;
            rest /= alphabet_length;
            chars.push((n as u8 + char_offset) as char);

            if rest == 0 {
                break;
            }
            rest -= 1
        }

        self.uid += 1;
        chars.into_iter().rev().collect()
    }
}

fn construct_uncovered_factbase(typ: Arc<Type>, guard_tree: Gdt) {
    let uncovered = u(
        FactBase {
            context: Var {
                name: 'x'.to_string(),
                typ: typ,
            },
            formula: None,
        },
        guard_tree,
    );

    println!("{} \n\n", uncovered);
}

fn u(fact_base: FactBase, clause: Gdt) -> FactBase {
    println!("u({}, {})", fact_base, clause);

    match clause {
        Gdt::Success => {
            let f = fact_base.add_fact(FactBaseFormula::Literal(FactBaseLiteral::False));

            println!("returning: {}\n", f);
            f
        }
        Gdt::Branch(branches) => {
            u(u(fact_base, *branches[0].clone()), *branches[1].clone())
            // TODO: Support arbitrary number of branches
            // branches.into_iter().fold(fact_base, |acc, branch| {
            //     u(u(fact_base, branch), )
            // })
        }
        Gdt::Construction { var, expr, t } => u(
            fact_base.add_fact(FactBaseFormula::Literal(FactBaseLiteral::Construction {
                var: var.clone(),
                expr: expr.clone(),
            })),
            *t,
        ),
        Gdt::Assignment { var, expr, t } => {
            let l = fact_base.add_fact(FactBaseFormula::Literal(FactBaseLiteral::DoesNotMatch {
                var: var.clone(),
                expr: expr.clone(),
            }));
            println!("l: {}", l);

            let r1 = fact_base.add_fact(FactBaseFormula::Literal(FactBaseLiteral::Assignment {
                var: var.clone(),
                expr: expr.clone(),
            }));
            println!("r1: {}", r1);

            let r = u(r1, *t);
            println!("r: {}", r);

            let i = l.union(r);
            println!("returning: {}\n", i);
            i
        }
    }
}
