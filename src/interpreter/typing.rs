use std::collections::HashMap;

use super::Metadata;
use crate::{
    interpreter::InterpreterError,
    parser::{Expression, Span, Statement},
    vec_map::MapInVec,
};
use std::fmt;

type ParserResult<T> = std::result::Result<T, super::InterpreterError>;

#[derive(Clone, PartialEq, Debug)]
pub enum Name {
    Integer,
    Text,
    Boolean,
    Function(u8),
    Nothing,
    List,
    Reference,
    Range,
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// TODO: This should not be possible 'let x = (x) -> x + [x]'
// TODO: This behaver might need to change 'let bird(c, x, y) = if c then x else y end'

#[derive(Clone, PartialEq)]
pub enum Type {
    Concrete(Name, Vec<Self>),
    Unknown(usize, Option<Vec<Self>>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Concrete(Name::Function(_), generics) => {
                let mut args = generics.map_ref(Type::to_string);
                let ret = args.remove(args.len() - 1);
                write!(f, "[({}) -> {}]", args.join(", "), ret,)
            }
            Self::Concrete(name, generics) => match generics.len() {
                0 => write!(f, "{}", name),
                _ => write!(
                    f,
                    "{}<{}>",
                    name,
                    generics.map_ref(Type::to_string).join(", ")
                ),
            },
            Self::Unknown(u, q) => match q {
                Some(q) => write!(f, "${} : {}", u, q.map_ref(Self::to_string).join(" or ")),
                None => write!(f, "${}", u),
            },
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Type {
    pub fn variable(&self) -> usize {
        match self {
            Self::Unknown(i, _) => *i,
            _ => panic!("Not of type Unknown"),
        }
    }

    pub fn nothing() -> Self {
        Type::Concrete(Name::Nothing, Vec::new())
    }

    pub fn integer() -> Self {
        Type::Concrete(Name::Integer, Vec::new())
    }

    pub fn text() -> Self {
        Type::Concrete(Name::Text, Vec::new())
    }

    pub fn boolean() -> Self {
        Type::Concrete(Name::Boolean, Vec::new())
    }

    pub fn list(t: Self) -> Self {
        Type::Concrete(Name::List, vec![t])
    }

    pub fn function(a: Vec<Self>) -> Self {
        Type::Concrete(Name::Function((a.len() - 1) as u8), a)
    }

    pub fn generic(i: usize) -> Self {
        Self::Unknown(i, None)
    }

    pub fn ret(&self) -> Self {
        match self {
            Self::Concrete(name, generics) => {
                if let Name::Function(_) = name {
                    generics.last().unwrap().clone()
                } else {
                    panic!("Not a function");
                }
            }
            _ => panic!("Not a function"),
        }
    }

    pub fn reference(t: Type) -> Self {
        Self::Concrete(Name::Reference, vec![t])
    }

    pub fn gen(&self, i: usize) -> Self {
        match self {
            Self::Concrete(_, generics) => generics[i].clone(),
            _ => panic!("Not a concrete"),
        }
    }

    pub fn range() -> Self {
        Type::Concrete(Name::Range, Vec::new())
    }

    pub fn bounded(i: usize, g: Vec<Self>) -> Self {
        Self::Unknown(i, Some(g))
    }
}

pub fn solve(
    tree: Vec<(Statement<Span>, Span)>,
    interp: &mut super::Interpreter,
    obj_scope: &HashMap<String, (Type, std::sync::Arc<std::sync::Mutex<super::Object>>)>,
) -> ParserResult<Vec<(Statement<Metadata>, Metadata)>> {
    let mut solver = Solver::new(interp);
    let mut scope = HashMap::new();

    for (name, (t, _)) in obj_scope {
        scope.insert(name.clone(), (t.clone(), true));
    }

    Ok(solver
        .solve_list(tree, &mut scope)?
        .map(|x| solver.rebase_statement(x)))
}

type Scope = HashMap<String, (Type, bool)>;

struct Solver<'a> {
    interp: &'a mut super::Interpreter,
    unknowns: Vec<Type>,
}

impl<'a> Solver<'a> {
    fn new(interp: &'a mut super::Interpreter) -> Self {
        Solver {
            interp,
            unknowns: Vec::new(),
        }
    }

    fn fresh_unknown(&mut self, q: Option<Vec<Type>>) -> Type {
        let i = self.unknowns.len();
        let t = Type::Unknown(i, q);
        self.unknowns.push(t.clone());
        t
    }

    fn solve_list(
        &mut self,
        statements: Vec<(Statement<Span>, Span)>,
        scope: &mut Scope,
    ) -> ParserResult<Vec<(Statement<Metadata>, Metadata)>> {
        statements
            .into_iter()
            .map(|s| self.solve_statement(s, scope))
            .collect()
    }

    fn solve_expected(
        &mut self,
        (expr, span): (Expression<Span>, Span),
        scope: &mut Scope,
        expected: Type,
    ) -> ParserResult<(Expression<Metadata>, Metadata)> {
        let (expr, metadata) = self.solve_expression((expr, span), scope)?;
        self.transmute(metadata.1.clone(), expected.clone()).ok_or(
            InterpreterError::MustBeType(
                metadata.0.clone(),
                self.source(expected),
                self.source(metadata.1.clone()),
            ),
        )?;
        Ok((expr, metadata))
    }

    fn solve_expression(
        &mut self,
        (expr, span): (Expression<Span>, Span),
        scope: &mut Scope,
    ) -> ParserResult<(Expression<Metadata>, Metadata)> {
        use Expression::*;

        Ok(match expr.clone() {
            Literal(n) => (Literal(n), (span, Type::integer())),
            String(s) => (String(s), (span, Type::text())),
            Boolean(b) => (Boolean(b), (span, Type::boolean())),
            Identifier(n) => {
                let t = self.genericise(
                    scope
                        .get(&n)
                        .ok_or(InterpreterError::CantFind(span.clone()))?
                        .clone(),
                    &mut HashMap::new(),
                );
                (Identifier(n), (span, t))
            }
            List(l) => {
                let list_t = self.fresh_unknown(None);

                let l = l
                    .into_iter()
                    .map(|e| self.solve_expected(e, scope, list_t.clone()))
                    .collect::<ParserResult<Vec<_>>>()?;

                (List(l), (span, Type::list(self.source(list_t))))
            }
            Call(id, args) => {
                let args_t = args
                    .into_iter()
                    .map(|e| self.solve_expression(e, scope))
                    .collect::<ParserResult<Vec<_>>>()?;

                let mut generics = args_t.clone().map(|t| t.1 .1);

                generics.push(self.fresh_unknown(None));

                let func_t = Type::function(generics);
                let id = self.solve_expected(*id, scope, func_t.clone())?;

                (
                    Call(Box::new(id), args_t),
                    (span, self.source(func_t.ret())),
                )
            }
            Lambda(args, body) => {
                let args_t = args.map_ref(|_| self.fresh_unknown(None));

                let mut new_scope = scope.clone();

                for (name, t) in args.iter().zip(args_t.iter()) {
                    new_scope.insert(name.clone(), (t.clone(), false));
                }

                let body = self.solve_expression(*body, &mut new_scope)?;

                let mut generics = args_t.map(|t| self.source(t));
                generics.push(self.source(body.1 .1.clone()));

                (
                    Lambda(args, Box::new(body)),
                    (span, Type::function(generics)),
                )
            }
            Reference(x) => {
                let x = self.solve_expression(*x, scope)?;
                let t = Type::reference(x.1 .1.clone());
                (Reference(Box::new(x)), (span, t))
            }
            Dereference(x) => {
                let expected = Type::reference(self.fresh_unknown(None));
                let x = self.solve_expected(*x, scope, expected.clone())?;
                (
                    Dereference(Box::new(x)),
                    (span, self.source(self.source(expected).gen(0))),
                )
            }
            ListIndex(list, idx) => {
                if let Ok(idx) = self.solve_expected(*idx.clone(), scope, Type::range()) {
                    let expected = Type::list(self.fresh_unknown(None));
                    let list = self.solve_expected(*list, scope, expected.clone())?;
                    (
                        ListIndex(Box::new(list), Box::new(idx)),
                        (span, Type::list(self.source(self.source(expected).gen(0)))),
                    )
                } else {
                    let idx = self.solve_expected(*idx, scope, Type::integer())?;

                    let expected = Type::list(self.fresh_unknown(None));
                    let list = self.solve_expected(*list, scope, expected.clone())?;
                    (
                        ListIndex(Box::new(list), Box::new(idx)),
                        (span, self.source(self.source(expected).gen(0))),
                    )
                }
            }
            Range(from, to) => {
                let from = self.solve_expected(*from, scope, Type::integer())?;
                let to = self.solve_expected(*to, scope, Type::integer())?;

                (Range(Box::new(from), Box::new(to)), (span, Type::range()))
            }
            DoList(statements) => {
                let statements = self.solve_list(statements, scope)?;
                let t = statements
                    .last()
                    .map(|s| s.1 .1.clone())
                    .unwrap_or(Type::nothing());
                (DoList(statements), (span, t))
            }
            If(pred, tru, fal) => {
                let pred = self.solve_expected(*pred, scope, Type::boolean())?;
                let tru = self.solve_list(tru, scope)?;

                if let Some(fal) = fal {
                    let tru_t = tru
                        .last()
                        .map(|s| s.1 .1.clone())
                        .unwrap_or(Type::nothing());
                    let fal = self.solve_list(fal, scope)?;

                    let fal_t = fal
                        .last()
                        .map(|s| s.1 .1.clone())
                        .unwrap_or(Type::nothing());
                    if self.transmute(fal_t, tru_t.clone()).is_some() {
                        (
                            If(Box::new(pred), tru, Some(fal)),
                            (span, self.source(tru_t)),
                        )
                    } else {
                        (If(Box::new(pred), tru, Some(fal)), (span, Type::nothing()))
                    }
                } else {
                    (If(Box::new(pred), tru, None), (span, Type::nothing()))
                }
            }
            Directive(name, args) => {
                // let args = args
                //     .into_iter()
                //     .map(|e| self.solve_expression(e, scope))
                //     .collect::<ParserResult<Vec<_>>>()?;

                let d = super::directive(self.interp, name, args)?;
                self.solve_expression(d, scope)?
            }
        })
    }

    fn rebase(&self, t: Metadata) -> Metadata {
        (t.0, self.source(t.1))
    }

    fn rebase_statement(
        &self,
        tree: (Statement<Metadata>, Metadata),
    ) -> (Statement<Metadata>, Metadata) {
        (
            match tree.0 {
                Statement::Expression(e) => Statement::Expression(self.rebase_expression(e)),
                Statement::Assignment(id, args, body) => {
                    Statement::Assignment(id, args, self.rebase_expression(body))
                }
                Statement::Reassignment(f, e) => {
                    Statement::Reassignment(self.rebase_expression(f), self.rebase_expression(e))
                }
                _ => todo!(),
            },
            self.rebase(tree.1),
        )
    }

    fn rebase_expression(
        &self,
        tree: (Expression<Metadata>, Metadata),
    ) -> (Expression<Metadata>, Metadata) {
        use Expression::*;

        (
            match tree.0 {
                t @ Literal(_) | t @ Identifier(_) | t @ Boolean(_) | t @ String(_) => t,
                List(items) => List(items.map(|e| self.rebase_expression(e))),
                Call(id, items) => Call(
                    Box::new(self.rebase_expression(*id)),
                    items.map(|e| self.rebase_expression(e)),
                ),
                Lambda(args, body) => Lambda(args, Box::new(self.rebase_expression(*body))),
                Reference(e) => Reference(Box::new(self.rebase_expression(*e))),
                Dereference(e) => Dereference(Box::new(self.rebase_expression(*e))),
                ListIndex(list, idx) => ListIndex(
                    Box::new(self.rebase_expression(*list)),
                    Box::new(self.rebase_expression(*idx)),
                ),
                Range(from, to) => Range(
                    Box::new(self.rebase_expression(*from)),
                    Box::new(self.rebase_expression(*to)),
                ),
                If(pred, body, else_) => If(
                    Box::new(self.rebase_expression(*pred)),
                    body.map(|e| self.rebase_statement(e)),
                    else_.map(|x| x.map(|e| self.rebase_statement(e))),
                ),
                DoList(list) => DoList(list.map(|e| self.rebase_statement(e))),
                Directive(name, args) => Directive(name, args.map(|e| self.rebase_expression(e))),
            },
            self.rebase(tree.1),
        )
    }

    // (x y) -> red(y, x)

    fn genericise(&mut self, (t, should): (Type, bool), map: &mut HashMap<usize, usize>) -> Type {
        if !should {
            return t;
        }

        match t {
            Type::Concrete(n, g) => Type::Concrete(n, g.map(|t| self.genericise((t, true), map))),
            Type::Unknown(i, q) => {
                let q = q.map(|o| o.map(|t| self.genericise((t, true), map)));
                Type::Unknown(
                    *map.entry(i)
                        .or_insert(self.fresh_unknown(q.clone()).variable()),
                    q,
                )
            }
        }
    }

    fn source(&self, t: Type) -> Type {
        self.source_trace(t, &mut Vec::new())
    }

    fn source_trace(&self, t: Type, hit: &mut Vec<usize>) -> Type {
        match t {
            Type::Unknown(i, _) if !hit.contains(&i) => {
                hit.push(i);
                self.source_trace(self.unknowns[i].clone(), hit)
            }
            Type::Concrete(n, g) => Type::Concrete(n, g.map(|t| self.source_trace(t, hit))),
            _ => t,
        }
    }

    fn assign(&mut self, i: usize, t: Type) {
        match self.source(Type::Unknown(i, None)) {
            Type::Unknown(j, _) => self.unknowns[j] = t.clone(),
            _ => unreachable!(),
        }

        assert!(self.source(self.unknowns[i].clone()) == self.source(t));
    }

    fn transmute(&mut self, a: Type, b: Type) -> Option<()> {
        use Type::*;

        match (self.source(a), self.source(b)) {
            (Concrete(ida, gena), Concrete(idb, genb)) => {
                if ida != idb {
                    return None;
                }

                for (a, b) in gena.into_iter().zip(genb) {
                    if self.transmute(a, b).is_none() {
                        return None;
                    }
                }

                Some(())
            }
            (Unknown(i, q), Unknown(j, g)) => {
                match (q, g) {
                    (Some(q), Some(g)) => {
                        let mut matching = Vec::new();
                        for q in &q {
                            for g in &g {
                                if self.transmute(q.clone(), g.clone()).is_some() {
                                    matching.push(q.clone());
                                }
                            }
                        }

                        self.assign(j, Type::Unknown(i, None));

                        match matching.len() {
                            0 => return None,
                            1 => self.assign(i, matching.remove(0)),
                            _ => self.assign(i, Type::Unknown(i, Some(matching))),
                        }
                    }
                    (Some(q), None) => self.assign(j, Unknown(i, Some(q))),
                    (None, Some(g)) => self.assign(i, Unknown(j, Some(g))),
                    _ => self.assign(i, Unknown(j, None)),
                }

                Some(())
            }
            (Unknown(i, q), t) | (t, Unknown(i, q)) => {
                if let Some(q) = q {
                    let mut matching = Vec::new();
                    for q in q {
                        if self.transmute(q.clone(), t.clone()).is_some() {
                            matching.push(q);
                        }
                    }

                    match matching.len() {
                        0 => return None,
                        1 => self.assign(i, matching.remove(0)),
                        _ => self.assign(i, Type::Unknown(i, Some(matching))),
                    }
                } else {
                    self.assign(i, t);
                }
                Some(())
            }
        }
    }

    fn solve_statement(
        &mut self,
        (statement, span): (Statement<Span>, Span),
        scope: &mut Scope,
    ) -> ParserResult<(Statement<Metadata>, Metadata)> {
        use Statement::*;

        Ok(match statement {
            Expression(expr) => {
                let expr = self.solve_expression(expr, scope)?;
                let m = expr.1.clone();
                (Expression(expr), m)
            }
            Assignment(name, args, value) => {
                if let Some(args) = args {
                    let args_t = args.map_ref(|_| self.fresh_unknown(None));

                    let mut gen_t = args_t.clone();
                    let ret_t = self.fresh_unknown(None);
                    gen_t.push(ret_t.clone());

                    let t = self.fresh_unknown(None);
                    self.unknowns[t.variable()] = Type::function(gen_t);
                    scope.insert(name.clone(), (t.clone(), false));

                    let mut new_scope = scope.clone();

                    for (name, t) in args.iter().zip(args_t.iter()) {
                        new_scope.insert(name.clone(), (t.clone(), false));
                    }

                    let body = self.solve_expected(value, &mut new_scope, ret_t)?;

                    let mut generics = args_t.map(|t| self.source(t));
                    generics.push(self.source(body.1 .1.clone()));

                    (
                        Assignment(name, Some(args), (body.0, (body.1 .0, self.source(t)))),
                        (span, Type::nothing()),
                    )
                } else {
                    let t = self.fresh_unknown(None);
                    scope.insert(name.clone(), (t.clone(), false));
                    let expr = self.solve_expected(value, scope, t)?;
                    (Assignment(name, None, expr), (span, Type::nothing()))
                }
            }
            Reassignment(f, e) => {
                let t = self.fresh_unknown(None);
                let f = self.solve_expected(f, scope, t.clone())?;
                let e = self.solve_expected(e, scope, t)?;

                (Reassignment(f, e), (span, Type::nothing()))
            }
            _ => todo!(),
        })
    }
}
