use crate::ast::{
    BindingKind, CallArg, ClauseGuard, Constant, Pattern, TypedClauseGuard, TypedPattern,
};
use crate::typ::{Error, Typer, ValueConstructorVariant};

pub enum GuardTreeNode {
    // Construct {
    //     var_name: String,
    //     expr: TypedClauseGuard,
    // },
    Match {
        var_name: String,
        expr: TypedClauseGuard,
    },
}

pub type GuardTree = Vec<GuardTreeNode>;
pub type Uncovered = Vec<Vec<TypedClauseGuard>>;

pub fn construct(pattern: &TypedPattern) -> GuardTree {
    let mut guard_tree: GuardTree = vec![];

    desugar(&mut guard_tree, pattern);

    guard_tree
}

fn desugar(guard_tree: &mut GuardTree, pattern: &TypedPattern) {
    match pattern {
        Pattern::Constructor {
            location,
            module,
            name,
            args,
            ..
        } => {
            guard_tree.push(GuardTreeNode::Match {
                var_name: "test".to_string(),
                expr: ClauseGuard::Constant(Constant::Record {
                    location: location.clone(),
                    module: module.clone(),
                    name: name.clone(),
                    args: vec![],
                    tag: name.clone(),
                    typ: crate::typ::int(), // TODO: Use real type
                }),
            });

            args.into_iter().for_each(|arg| {
                let CallArg { value, .. } = arg;

                desugar(guard_tree, value)
            })
        }
        _ => (),
    }
}

pub fn construct_uncovered<'a, 'b>(
    guard_tree: GuardTree,
    typer: &'a Typer<'b>,
    kind: &BindingKind,
) -> Result<Uncovered, Error> {
    guard_tree
        .iter()
        .map(|t| {
            match t {
                // GuardTreeNode::Construct { .. } => Ok(vec![]),
                GuardTreeNode::Match { expr, .. } => {
                    let uncovered = generate_uncovered(expr, typer);

                    // Ensure exhaustiveness of constructor if this is a `let` or `try` binding
                    if [BindingKind::Let, BindingKind::Try].contains(kind) {
                        if uncovered.len() > 0 {
                            // lol this sucks
                            match expr {
                                ClauseGuard::Constant(constant) => match constant {
                                    Constant::Record { name, .. } => {
                                        let constructor =
                                            typer.get_value_constructor(None, name).unwrap();

                                        match &constructor.variant {
                                            ValueConstructorVariant::Record {
                                                other_constructor_names,
                                                ..
                                            } => {
                                                return Err(Error::NonExhaustiveBinding {
                                                    location: expr.location().clone(),
                                                    constructor: name.clone(),
                                                    kind: kind.clone(),
                                                    unhandled_constructors: other_constructor_names
                                                        .clone(),
                                                });
                                            }
                                            _ => (),
                                        }
                                    }
                                    _ => (),
                                },
                                _ => (),
                            }
                        }
                    }

                    Ok(uncovered)
                }
            }
        })
        .collect::<Result<Vec<_>, Error>>()
}

fn generate_uncovered<'a, 'b>(
    expr: &TypedClauseGuard,
    typer: &'a Typer<'b>,
) -> Vec<TypedClauseGuard> {
    // dbg!(expr);
    match expr {
        ClauseGuard::Constant(constant) => {
            // dbg!(constant);
            match constant {
                // Constant::Int {
                //     location, value, ..
                // } => Ok(Constant::Int { location, value }),

                // Constant::Float {
                //     location, value, ..
                // } => Ok(Constant::Float { location, value }),

                // Constant::String {
                //     location, value, ..
                // } => Ok(Constant::String { location, value }),

                // Constant::Tuple {
                //     elements, location, ..
                // } => self.infer_const_tuple(elements, location),

                // Constant::List {
                //     elements, location, ..
                // } => self.infer_const_list(elements, location),

                // Constant::BitString { location, segments } => {
                //     self.infer_constant_bit_string(segments, location)
                // }
                Constant::Record {
                    module,
                    location,
                    typ,
                    tag,
                    ..
                } => {
                    let constructor = typer.get_value_constructor(module.as_ref(), tag).unwrap();

                    // dbg!(constructor);

                    match &constructor.variant {
                        ValueConstructorVariant::Record {
                            other_constructor_names,
                            ..
                        } => other_constructor_names
                            .iter()
                            .cloned()
                            .map(|c| {
                                ClauseGuard::Constant(Constant::Record {
                                    location: location.clone(),
                                    module: module.clone(),
                                    name: c.clone(),
                                    args: vec![],
                                    tag: c,
                                    typ: typ.clone(),
                                })
                            })
                            .collect(),

                        _ => vec![],
                    }
                }

                _ => vec![],
            }
        }
        _ => vec![],
    }
}
