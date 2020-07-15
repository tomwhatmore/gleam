use crate::ast::{CallArg, Pattern, TypedClause, TypedPattern};
use crate::typ::{Type, Typer};

use std::fmt;
use std::sync::Arc;

#[derive(Debug, PartialEq, Clone)]
struct Constructor {
    name: String,
}

impl fmt::Display for Constructor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, PartialEq, Clone)]
struct Var {
    name: String,
    typ: Option<Arc<Type>>,
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: Maybe T", self.name) // TODO: Real type
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
enum Expr {
    Var(Var),

    Construction {
        constructor: Constructor,
        args: Vec<String>,
    },
}

impl Expr {
    fn name(&self) -> String {
        match self {
            Expr::Var(v) => v.name.clone(),

            Expr::Construction { constructor: Constructor { name }, ..} => name.clone(),
        }
    }

    fn new_construction(name: &String, args: &Vec<String>) -> Self {
        Expr::Construction {
            constructor: Constructor { name: name.clone() },
            args: args.clone(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Var(v) => write!(f, "{}", v.name),
            Expr::Construction { constructor: Constructor { name }, args, .. } if args.len() > 0 => {
                write!(f, "{} {}", name, args.join(" "))
            }
            Expr::Construction { constructor: Constructor { name }, .. } => write!(f, "{}", name),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
enum Gdt {
    Construction {
        var: Box<Var>,
        expr: Box<Expr>,
        t: Box<Self>,
    },

    Assignment {
        var: Box<Var>,
        expr: Box<Expr>,
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
            Gdt::Branch(branches) if branches.len() > 1 => write!(
                f,
                "\nGuard Tree\n━━┳━┫{}\n  ┃\n  ┗━┫{}\n",
                branches[0], branches[1]
            ),
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
        var: Var,
        constructor: Constructor,
    },
    Assignment {
        var: Box<Var>,
        expr: Box<Expr>,
    },
    Construction {
        var: Box<Var>,
        expr: Box<Expr>,
    },
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::True => write!(f, "✓"),
            Literal::False => write!(f, "✗"),
            Literal::DoesNotMatch { var, constructor } => write!(f, "{} ≉ {}", var, constructor.name),
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
    context: Vec<Var>,
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
// ⟨a: Maybe T | a ≉ Just ∨ (Just b ← a ∧ (b ≉ A ∨ (A ← b ∧ (✗))))⟩

impl fmt::Display for RefinementType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "⟨{} | {}⟩", self.context.first().unwrap(), self.formula) // TODO: print entire context
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
enum Constraint {
    TypeConstraint,

    DoesNotMatch {
        var: Var,
        constructor: Constructor,
    },

    MatchVar(Box<Var>, Box<Var>),

    MatchExpr(Box<Var>, Box<Expr>),
}

#[derive(Debug, PartialEq, Clone)]
enum NormalisedRefinementType {
    False,
    True {
        context: Vec<Var>,
        constraints: Vec<Box<Constraint>>,
    },
}

impl NormalisedRefinementType {
    fn union(&self, other_nrt: NormalisedRefinementType) -> Self {
        match (self, other_nrt) {
            (
                NormalisedRefinementType::True {
                    context,
                    constraints,
                },
                NormalisedRefinementType::True {
                    constraints: other_constraints,
                    ..
                },
            ) => {
                let mut new_constraints = constraints.clone();
                other_constraints
                    .into_iter()
                    .for_each(|c| new_constraints.push(c));

                NormalisedRefinementType::True {
                    context: context.clone(),
                    constraints: new_constraints,
                }
            }
            _ => NormalisedRefinementType::False,
        }
    }

    fn add_formula_literal(&self, literal: Literal) -> Self {
        match literal {
            Literal::True => self.clone(),
            Literal::False => NormalisedRefinementType::False,

            Literal::Assignment { var, expr } => {
                // Need to refactor ClauseExpr to have different variants to handle properly
                // Currently handling the case where it's a construction and array of vars only

                self.add_to_context(*var)
            },

            Literal::Construction { var, .. } => {
                // TODO: line 644 - 648, three options depending on type of construction
                // Need to refactor ClauseExpr to have different variants to handle properly
                // Currently handling only the last, simplest case let x: τ = e

                self.add_to_context(*var)
            },

            Literal::DoesNotMatch { var, constructor } => {
                self.add_constraint(Constraint::DoesNotMatch {
                    var: var.clone(),
                    constructor: constructor.clone(),
                })
            },
        }
    }

    //
    fn add_constraint(&mut self, constraint: Constraint) -> Self {
        match self {
            NormalisedRefinementType::False => NormalisedRefinementType::False,
            NormalisedRefinementType::True { context, constraints} => {
                match &constraint {
                    // :654
                    Constraint::TypeConstraint => {
                        // TODO

                        self.clone()
                    },

                    // :657
                    Constraint::MatchExpr(lhs, rhs) => {

                    },

                    // :661
                    Constraint::DoesNotMatch { var, constructor } => {
                        // ∆(x)
                        let v = self.find_representation_of(*var);

                        // × if ∆(x) ≈ K a y ∈ ∆
                        if constraints.iter().find(|c| {
                            if let Constraint::MatchExpr(lhs, rhs) = ***c {
                                *lhs == v && *rhs.name() == constructor.name
                            } else {
                                false
                            }
                        }).is_some() {
                            return NormalisedRefinementType::False
                        }

                        // × if not ⟨Γ || (∆, ∆(x) ≉ K)⟩ ⊢ ∆(x)
                        // TODO

                        // otherwise

                        constraints.push(Box::new(constraint));
                        *self
                    },

                    // :671
                    Constraint::MatchVar(x, y) => {
                        // x′ = ∆(x) and y′ = ∆(y)
                        let x_prime = self.find_representation_of(**x);
                        let y_prime = self.find_representation_of(**y);

                        if x_prime == y_prime {
                            // ⟨Γ || ∆⟩ if x′ = y′
                            self.clone()
                        } else {
                            // ⟨Γ || ((∆\x′), x′ ≈ y′)⟩ ⊕δ (∆|x′ [y′/x′] otherwise
                            // TODO: No idea what ∆\x′ or ∆|x′ [y′/x′] mean
                            constraints.push(Box::new(Constraint::MatchVar(Box::new(x_prime), Box::new(y_prime))));
                            *self
                        }
                    },
                }
            }
        }
    }

    fn add_to_context(&self, var: Var) -> Self {
        match self {
            NormalisedRefinementType::False => NormalisedRefinementType::False,
            NormalisedRefinementType::True { context, constraints} => {
                let mut context = context.clone();
                context.push(var);

                NormalisedRefinementType::True {
                    context,
                    constraints: constraints.clone(),
                }
            }
        }
    }

    // ∆(x) :580
    fn find_representation_of(&self, var: Var) -> Var {
        match self {
            NormalisedRefinementType::False => unreachable!(), // This shouldn't be possible
            NormalisedRefinementType::True { constraints, ..} => {
                let rhs = constraints.iter().find_map(|c| {
                    if let Constraint::MatchVar(lhs, rhs) = **c {
                        if lhs.name == var.name {
                            Some(self.find_representation_of(*rhs))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });

                rhs.unwrap_or(var)
            }
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

    pub fn check_pattern(&mut self, pattern: &TypedPattern, typ: Arc<Type>) {
        let gdt = self.desugar_pattern(pattern, Some("x".to_string()), Gdt::Success(1));
        println!("{}", gdt);
        construct_refinement_type(typ, gdt);
    }

    pub fn check_clauses(&mut self, clauses: &Vec<TypedClause>, typs: Vec<Arc<Type>>) {
        let subject = self.next_variable_name();
        let branches = clauses
            .into_iter()
            .enumerate()
            .map(|(index, clause)| {
                Box::new(self.desugar_pattern(
                    clause.pattern.first().unwrap(),
                    Some(subject.clone()),
                    Gdt::Success(index + 1),
                ))
            })
            .collect();

        let gdt = Gdt::Branch(branches);
        println!("{}", gdt);
        construct_refinement_type(typs.first().unwrap().clone(), gdt);
    }

    fn desugar_pattern(
        &mut self,
        pattern: &TypedPattern,
        var_name: Option<String>,
        mut t: Gdt,
    ) -> Gdt {
        match pattern {
            Pattern::Constructor {
                name, args, ..
            } => {
                let var = Box::new(Var {
                    typ: None, // TODO: Typ
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
                    expr: Box::new(Expr::new_construction(&name, &vars)),
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

    // Cons(⟨Γ || ∆⟩, τ) = Ks :746
    fn constructors(&self, nrt: NormalisedRefinementType, typ: Arc<Type>) -> Vec<Constructor> {
        // TODO: Need a better way to get constructors from a typ!
        match &*typ {
            Type::App { ref name, .. } => {
                // self
                // .typer
                // .get_type_constructor(module, name)
                // .unwrap()
                // .clone(),

                // TODO obviously
                if name == "Maybe" {
                    return vec![Constructor { name: "Just".to_string() }, Constructor { name: "Nothing".to_string() }]
                } else {
                    return vec![Constructor { name: "A".to_string() }, Constructor { name: "B".to_string() }, Constructor { name: "C".to_string() }]
                }
            }
            Type::Fn { retrn, .. } => match &**retrn {
                Type::App { ref name, .. } => {
                    // self
                    // .typer
                    // .get_type_constructor(module, name)
                    // .unwrap()
                    // .clone(),

                    // TODO obviously
                    if name == "Maybe" {
                        return vec![Constructor { name: "Just".to_string() }, Constructor { name: "Nothing".to_string() }]
                    } else {
                        return vec![Constructor { name: "A".to_string() }, Constructor { name: "B".to_string() }, Constructor { name: "C".to_string() }]
                    }
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
    }

    // Inst(⟨Γ || ∆⟩, x, K) :753
    fn instantiate(&self, nrt: NormalisedRefinementType, _var: Var, _constructor: Constructor) -> NormalisedRefinementType {
        nrt
    }
}

fn construct_refinement_type(typ: Arc<Type>, guard_tree: Gdt) {
    let uncovered = u(
        RefinementType {
            context: vec![Var {
                name: "a".to_string(),
                typ: Some(typ),
            }],
            formula: Formula::Literal(Literal::True),
        },
        guard_tree,
    );

    println!("{} \n\n", uncovered);
}

fn u(refinement_type: RefinementType, clause: Gdt) -> RefinementType {
    // println!("u({}, {})", fact_base, clause);

    match clause {
        Gdt::Success(_) => {
            let f = RefinementType {
                context: refinement_type.context.clone(),
                formula: Formula::Literal(Literal::False),
            };

            // println!("returning: {}\n", f);
            f
        }

        // :451
        Gdt::Branch(branches) if branches.len() > 1 => {
            u(
                u(refinement_type, *branches[0].clone()),
                *branches[1].clone(),
            )
            // TODO: Support arbitrary number of branches
            // branches.into_iter().fold(fact_base, |acc, branch| {
            //     u(u(fact_base, branch), )
            // })
        }
        Gdt::Branch(branches) => u(refinement_type, *branches[0].clone()),

        // U(Θ, Guard(let x = e) t) = U(Θ ⩑ (let x = e), t)
        // :453
        Gdt::Construction { var, expr, t } => u(
            refinement_type.add_fact(Formula::Literal(Literal::Construction {
                var: var.clone(),
                expr: expr.clone(),
            })),
            *t,
        ),

        // :454
        Gdt::Assignment { var, expr, t } => {
            let constructor = match &*expr {
                Expr::Construction { constructor, ..} => constructor,
                _ => unreachable!()
            };

            let l = refinement_type.add_fact(Formula::Literal(Literal::DoesNotMatch {
                var: *var,
                constructor: constructor.clone(),
            }));
            // println!("l: {}", l);

            let r = u(refinement_type, *t);
            // println!("r: {}", r);

            let r1 = r.add_fact(Formula::Literal(Literal::Assignment {
                var: var.clone(),
                expr: expr.clone(),
            }));

            let i = l.union(r1);
            // println!("returning: {}\n", i);
            i
        }
    }
}

fn normalise_refinement_type(refinement_type: RefinementType) -> NormalisedRefinementType {
    c(
        NormalisedRefinementType::True {
            context: refinement_type.context.clone(),
            constraints: vec![],
        },
        refinement_type.formula,
    )
}

fn c(nrt: NormalisedRefinementType, formula: Formula) -> NormalisedRefinementType {
    match formula {
        Formula::Literal(l) => nrt.add_formula_literal(l),

        Formula::Intersection { lhs, rhs } => {
            let left_prime = c(nrt, *lhs);
            let right = c(left_prime.clone(), *rhs);

            right.union(left_prime)
        }

        Formula::Union { lhs, rhs } => c(nrt.clone(), *lhs).union(c(nrt, *rhs)),
    }
}
