use crate::ast::{CallArg, Pattern, TypedPattern, TypedClause};
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
            ClauseExpr::RecordConstructor { name, args, .. } if args.len() > 0 => {
                write!(f, "{} {}", name, args.join(" "))
            }
            ClauseExpr::RecordConstructor { name, .. } => write!(f, "{}", name),
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

    Success(usize),
    // Original Haskell version has ! as well
}

impl fmt::Display for Gdt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Gdt::Construction { var, expr, t } => write!(f, "let {} = {}, {}", var, expr, t),
            Gdt::Assignment { var, expr, t } => write!(f, "{} ← {}, {}", expr, var, t),
            Gdt::Branch(branches) if branches.len() > 1 => write!(f, "\nGuard Tree\n━━┳━┫{}\n  ┃\n  ┗━┫{}\n", branches[0], branches[1]),
            Gdt::Branch(branches) => write!(f, "{}", branches[0]),
            Gdt::Success(i) => write!(f, "-> {}", i),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Literal {
    True,
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

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::True => write!(f, "✓"),
            Literal::False => write!(f, "✗"),
            Literal::DoesNotMatch { var, expr } => write!(f, "{} ≉ {}", var, expr.name()),
            Literal::Assignment { var, expr } => write!(f, "{} ← {}", expr, var),
            Literal::Construction { var, expr } => write!(f, "let {} = {}", var, expr),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Formula {
    Union { lhs: Box<Self>, rhs: Box<Self> },

    Intersection { lhs: Box<Self>, rhs: Box<Self> },

    Literal(Literal),
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::Union { lhs, rhs } => write!(f, "{} ∨ ({})", lhs, rhs),
            Formula::Intersection { lhs, rhs } => write!(f, "{} ∧ ({})", lhs, rhs),
            Formula::Literal(l) => write!(f, "{}", l),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct RefinementType {
    context: Var,
    formula: Formula,
}

impl RefinementType {
    fn add_fact(&self, formula: Formula) -> RefinementType {
        match self.formula {
            Formula::Literal(Literal::True) => RefinementType {
                context: self.context.clone(),
                formula: formula.clone(),
            },
            _ => RefinementType {
                context: self.context.clone(),
                formula: Formula::Intersection {
                    lhs: Box::new(formula.clone()),
                    rhs: Box::new(self.formula.clone()),
                },
            },
        }
    }

    fn union(&self, other_factbase: RefinementType) -> RefinementType {
        RefinementType {
            context: self.context.clone(),
            formula: Formula::Union {
                lhs: Box::new(self.formula.clone()),
                rhs: Box::new(other_factbase.formula.clone()),
            },
        }
    }
}

impl fmt::Display for RefinementType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "⟨{}: Maybe A | {}⟩", self.context.name, self.formula)
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

    pub fn check_pattern(&mut self, pattern: &TypedPattern, typ: Arc<Type>) {
        let gdt = self.desugar_pattern(pattern, Some("x".to_string()), Gdt::Success(1));
        println!("{}", gdt);
        construct_uncovered_factbase(typ, gdt);
    }

    pub fn check_clauses(&mut self, clauses: &Vec<TypedClause>, typs: Vec<Arc<Type>>) {
        let subject = self.next_variable_name();
        let branches = clauses.into_iter().enumerate().map(|(index, clause)| {
            Box::new(self.desugar_pattern(clause.pattern.first().unwrap(), Some(subject.clone()), Gdt::Success(index + 1)))
        }).collect();

        let gdt = Gdt::Branch(branches);
        println!("{}", gdt);
        construct_uncovered_factbase(typs.first().unwrap().clone(), gdt);
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
                    name: var_name.unwrap_or_else(|| self.next_variable_name()),
                });

                let mut vars = vec![];

                args.into_iter().rev().for_each(|arg| {
                    let CallArg { value, .. } = arg;
                    let name = self.next_variable_name();
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

    fn next_variable_name(&mut self) -> String {
        let alphabet_length = 26;
        let char_offset = 97;
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
        RefinementType {
            context: Var {
                name: 'x'.to_string(),
                typ: typ,
            },
            formula: Formula::Literal(Literal::True),
        },
        guard_tree,
    );

    println!("{} \n\n", uncovered);
}

fn u(fact_base: RefinementType, clause: Gdt) -> RefinementType {
    // println!("u({}, {})", fact_base, clause);

    match clause {
        Gdt::Success(_) => {
            let f = RefinementType {
                context: fact_base.context.clone(),
                formula: Formula::Literal(Literal::False),
            };

            // println!("returning: {}\n", f);
            f
        },
        Gdt::Branch(branches) if branches.len() > 1 => {
            u(u(fact_base, *branches[0].clone()), *branches[1].clone())
            // TODO: Support arbitrary number of branches
            // branches.into_iter().fold(fact_base, |acc, branch| {
            //     u(u(fact_base, branch), )
            // })
        }
        Gdt::Branch(branches) => {
            u(fact_base, *branches[0].clone())
        },
        Gdt::Construction { var, expr, t } => u(
            fact_base.add_fact(Formula::Literal(Literal::Construction {
                var: var.clone(),
                expr: expr.clone(),
            })),
            *t,
        ),
        Gdt::Assignment { var, expr, t } => {
            let l = fact_base.add_fact(Formula::Literal(Literal::DoesNotMatch {
                var: var.clone(),
                expr: expr.clone(),
            }));
            // println!("l: {}", l);

            let r = u(fact_base, *t);
            // println!("r: {}", r);

            let r1 = r.add_fact(Formula::Literal(Literal::Assignment {
                var: var.clone(),
                expr: expr.clone(),
            }));

            let i = l.union(r1);
            // println!("returning: {}\n", i);
            i
        },
    }
}
