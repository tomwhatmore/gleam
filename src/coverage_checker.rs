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
    },
}

impl fmt::Display for ClauseExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ClauseExpr::Var(v) => write!(f, "{}", v.name),
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

impl fmt::Display for FactBaseLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FactBaseLiteral::True => write!(f, "✓"),
            FactBaseLiteral::False => write!(f, "✗"),
            FactBaseLiteral::DoesNotMatch { var, expr } => write!(f, "{} ≉ {}", var, expr),
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
            FactBaseFormula::Union { lhs, rhs } => write!(f, "{} ∨ ({})", lhs, rhs),
            FactBaseFormula::Intersection { lhs, rhs } => write!(f, "{} ∧ ({})", lhs, rhs),
            FactBaseFormula::Literal(l) => write!(f, "{}", l),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
struct FactBase {
    context: Var,
    formula: FactBaseFormula,
}

impl FactBase {
    fn add_fact(&self, formula: FactBaseFormula) -> FactBase {
        FactBase {
            context: self.context.clone(),
            formula: FactBaseFormula::Union {
                lhs: Box::new(self.formula.clone()),
                rhs: Box::new(formula.clone()),
            },
        }
    }

    fn intersect(&self, other_factbase: FactBase) -> FactBase {
        FactBase {
            context: self.context.clone(),
            formula: FactBaseFormula::Intersection {
                lhs: Box::new(self.formula.clone()),
                rhs: Box::new(other_factbase.formula.clone()),
            },
        }
    }
}

impl fmt::Display for FactBase {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "⟨{}: Typ | {}⟩", self.context.name, self.formula)
        // write!(f, "<{}: {} | {}>", self.context.name, self.typ, self.formula) // TODO: Need to write display code for Type
    }
}

pub struct CoverageChecker<'a, 'b> {
    typer: &'a Typer<'b>,
    uid: usize,
}

impl<'a, 'b> CoverageChecker<'a, 'b> {
    pub fn new(typer: &'a Typer<'b>) -> Self {
        Self {
            typer,
            uid: 0,
        }
    }

    pub fn construct_guard_tree(&mut self, pattern: &TypedPattern, typ: Arc<Type>) {
        let gdt = self.desugar_pattern(pattern, Gdt::Success);
        println!("{}", gdt);
        construct_uncovered_factbase(typ, gdt);
    }

    fn desugar_pattern(
        &mut self,
        pattern: &TypedPattern,
        mut t: Gdt,
    ) -> Gdt {
        match pattern {
            Pattern::Constructor {
                module, name, args, ..
            } => {
                let constructor = self.typer.get_value_constructor(module.as_ref(), name).unwrap().clone();

                let type_constructor = match &*constructor.typ {
                    Type::App { ref name, .. } => self.typer.get_type_constructor(module, name).unwrap().clone(),
                    Type::Fn { retrn, .. } => match &**retrn {
                        Type::App { ref name, .. } => self.typer.get_type_constructor(module, name).unwrap().clone(),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                let expr = Box::new(ClauseExpr::RecordConstructor {
                        name: name.clone(),
                        type_constructor,
                    });

                let var = Box::new(Var {
                        typ: constructor.typ.clone(),
                        name: self.next_variable_name(true),
                    });

                args
                    .into_iter()
                    .rev()
                    .for_each(|arg| {
                        let CallArg { value, .. } = arg;

                        t = self.desugar_pattern(value, t.clone());
                    });

                Gdt::Assignment { expr, var, t: Box::new(t) }
            },
            _ => t,
        }
    }

    fn next_variable_name(&mut self, assignment: bool) -> String {
        let alphabet_length = 26;
        let char_offset = if assignment { 120 } else { 97 };
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
            formula: FactBaseFormula::Literal(FactBaseLiteral::True),
        },
        guard_tree,
    );

    println!("{}", uncovered);
}

fn u(fact_base: FactBase, clause: Gdt) -> FactBase {
    println!("u({}, {})", fact_base, clause);

    match clause {
        Gdt::Success => FactBase {
            context: fact_base.context.clone(),
            formula: FactBaseFormula::Literal(FactBaseLiteral::False),
        },
        Gdt::Branch(branches) => {
            u(u(fact_base, *branches[0].clone()), *branches[1].clone())
            // branches.into_iter().fold(fact_base, |acc, branch| {
            //     u(u(fact_base, branch), )
            // })
        }
        Gdt::Construction { var, expr , t } => u(
            fact_base.add_fact(FactBaseFormula::Literal(
                FactBaseLiteral::Construction { var: var.clone(), expr: expr.clone() },
            )),
            *t,
        ),
        Gdt::Assignment { var, expr, t } => {
            let l = fact_base
            .add_fact(FactBaseFormula::Literal(FactBaseLiteral::DoesNotMatch {
                var: var.clone(),
                expr: expr.clone(),
            }));
            println!("l: {}", l);

            let r = u(
                fact_base.add_fact(FactBaseFormula::Literal(
                    FactBaseLiteral::Assignment {
                        var: var.clone(),
                        expr: expr.clone(),
                    },
                )),
                *t,
            );
            println!("r: {}", l);

            let i = l.intersect(r);
            println!("intersect: {}", i);
            i
        }

    }
}
