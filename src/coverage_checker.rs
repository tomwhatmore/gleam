use crate::ast::{CallArg, Pattern, TypedPattern};
use crate::typ::{Type, TypeConstructor, Typer};
use std::sync::Arc;
use std::fmt;

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
enum GuardTreeClause {
    Construction {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
        next: Box<Self>,
    },

    Assignment {
        var: Box<Var>,
        expr: Box<ClauseExpr>,
        next: Box<Self>,
    },

    Branch(Vec<Box<Self>>),

    Success,
    // Original Haskell version has ! as well
}

pub fn construct_guard_tree<'a, 'b>(typer: &'a Typer<'b>, pattern: &TypedPattern, typ: Arc<Type>) {
    let guard_tree = desugar_pattern(typer, pattern, GuardTreeClause::Success);
    construct_uncovered_factbase(typ, guard_tree);
}

fn desugar_pattern<'a, 'b>(
    typer: &'a Typer<'b>,
    pattern: &TypedPattern,
    next: GuardTreeClause,
) -> GuardTreeClause {
    match pattern {
        Pattern::Constructor {
            module,
            name,
            args,
            ..
        } => {
            let constructor = typer.get_value_constructor(module.as_ref(), name).unwrap();

            let type_constructor = match &*constructor.typ {
                Type::App { ref name, .. } => typer.get_type_constructor(module, name).unwrap(),
                Type::Fn { retrn, .. } => match &**retrn {
                    Type::App { ref name, .. } => typer.get_type_constructor(module, name).unwrap(),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };

            let arg_clauses = args
                .into_iter()
                .map(|arg| {
                    let CallArg { value, .. } = arg;

                    desugar_pattern(typer, value, next.clone())
                })
                .collect::<Vec<GuardTreeClause>>();

            GuardTreeClause::Assignment {
                var: Box::new(Var {
                    name: "test".to_string(),
                    typ: constructor.typ.clone(),
                }),
                expr: Box::new(ClauseExpr::RecordConstructor {
                    name: name.clone(),
                    type_constructor: type_constructor.clone(),
                }),
                next: Box::new(if arg_clauses.is_empty() {
                    next.clone()
                } else {
                    arg_clauses.first().unwrap().clone()
                }),
            }
        }
        _ => next,
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
}

impl fmt::Display for FactBaseLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FactBaseLiteral::True => write!(f, "✓"),
            FactBaseLiteral::False => write!(f, "✗"),
            FactBaseLiteral::DoesNotMatch { var, expr } => write!(f, "{} ≈ {}", var, expr),
            FactBaseLiteral::Assignment { var, expr } => write!(f, "{} ← {}", expr, var)
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum FactBaseFormula {
    Union { lhs: Box<Self>, rhs: Box<Self> },

    Intersection { lhs: Box<Self>, rhs: Box<Self> },

    Literal(FactBaseLiteral)
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
    fn formula_intersection(&self, formula: FactBaseFormula) -> FactBase {
        FactBase {
            context: self.context.clone(),
            formula: FactBaseFormula::Intersection {
                lhs: Box::new(self.formula.clone()),
                rhs: Box::new(formula.clone()),
            },
        }
    }

    fn union(&self, other_factbase: FactBase) -> FactBase {
        FactBase {
            context: self.context.clone(),
            formula: FactBaseFormula::Union {
                lhs: Box::new(self.formula.clone()),
                rhs: Box::new(other_factbase.formula.clone()),
            },
        }
    }
}

impl fmt::Display for FactBase {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "⟨{}: Typ | {}⟩", self.context.name, self.formula)
        // write!(f, "<{}: {} | {}>", self.context.name, self.typ, self.formula) // Soon come
    }
}

fn construct_uncovered_factbase(
    typ: Arc<Type>,
    guard_tree: GuardTreeClause,
) {
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

fn u(fact_base: FactBase, clause: GuardTreeClause) -> FactBase {
    match clause {
        GuardTreeClause::Success => FactBase {
            context: fact_base.context.clone(),
            formula: FactBaseFormula::Literal(FactBaseLiteral::False),
        },
        // GuardTreeClause::Branch(branches) => {
        //     branches.into_iter().fold(fact_base, |acc, branch| {
        //         u(u(fact_base, branch), )
        //     })
        // }
        // GuardTreeClause::Construction { var, expr, next } => {

        // },
        GuardTreeClause::Assignment { var, expr, next } => fact_base
            .formula_intersection(FactBaseFormula::Literal(FactBaseLiteral::DoesNotMatch {
                var: var.clone(),
                expr: expr.clone(),
            }))
            .union(u(
                fact_base.formula_intersection(FactBaseFormula::Literal(FactBaseLiteral::Assignment {
                    var: var.clone(),
                    expr: expr.clone(),
                })),
                *next,
            )),

        _ => fact_base, // TODO
    }
}

// fn construct_uncovered_inhabitants() {

// }

// // Ensure exhaustiveness of constructor if this is a `let` or `try` binding
// if [BindingKind::Let, BindingKind::Try].contains(kind) {
//     if uncovered.len() > 0 {
//         // lol this sucks
//         match expr {
//             ClauseGuard::Constant(constant) => match constant {
//                 Constant::Record { name, .. } => {
//                     let constructor =
//                         typer.get_value_constructor(None, name).unwrap();

//                     match &constructor.variant {
//                         ValueConstructorVariant::Record {
//                             other_constructor_names,
//                             ..
//                         } => {
//                             return Err(Error::NonExhaustiveBinding {
//                                 location: expr.location().clone(),
//                                 constructor: name.clone(),
//                                 kind: kind.clone(),
//                                 unhandled_constructors: other_constructor_names
//                                     .clone(),
//                             });
//                         }
//                         _ => (),
//                     }
//                 }
//                 _ => (),
//             },
//             _ => (),
//         }
//     }
// }

// fn generate_uncovered<'a, 'b>(
//     clause: &GuardTreeClause,
//     typer: &'a Typer<'b>,
// ) -> FactBaseLiteral {
// dbg!(expr);

//     ClauseGuard::Constant(constant) => {
//         dbg!(constant);
//         match constant {
//             // I think lists are dfferent
//             // Constant::List {
//             //     elements, location, ..
//             // } => self.infer_const_list(elements, location),

//             Constant::Record {
//                 module,
//                 location,
//                 typ,
//                 tag,
//                 ..
//             } => {
//                 let constructor = typer.get_value_constructor(module.as_ref(), tag).unwrap();

//                 // dbg!(constructor);

//                 match &constructor.variant {
//                     ValueConstructorVariant::Record {
//                         other_constructor_names,
//                         ..
//                     } => other_constructor_names
//                         .iter()
//                         .cloned()
//                         .map(|c| {
//                             ClauseGuard::Constant(Constant::Record {
//                                 location: location.clone(),
//                                 module: module.clone(),
//                                 name: c.clone(),
//                                 args: vec![],
//                                 tag: c,
//                                 typ: typ.clone(),
//                             })
//                         })
//                         .collect(),

//                     _ => vec![],
//                 }
//             }

//             // All other constants cannot
//             _ => vec![],
//         }
//     }
//     _ => vec![],
// }
// }
