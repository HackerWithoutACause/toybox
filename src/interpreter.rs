pub mod typing;

use self::typing::Type;
use crate::{
    parser::{parser, Expression, Span, Statement},
    vec_map::MapInVec,
};
use chumsky::Parser;
use std::{
    collections::HashMap,
    fmt,
    sync::{Arc, Mutex},
};
use wasm_bindgen::prelude::*;

type Metadata = (Span, Type);
type ParserResult<T> = std::result::Result<T, InterpreterError>;

fn directive(
    interp: &mut Interpreter,
    name: String,
    mut args: Vec<(Expression<Span>, Span)>,
) -> ParserResult<(Expression<Span>, Span)> {
    Ok(match name.as_str() {
        "identifier" => {
            assert!(args.len() == 1);
            let first = args.remove(0);
            let id = &first.0.string().ok_or(InterpreterError::MustBeType(
                first.1.clone(),
                Type::text(),
                Type::nothing(),
            ))?;
            (Expression::Identifier(id.clone()), first.1.clone())
        }
        "typed" => {
            if args.len() != 1 {
                return Err(InterpreterError::MismatchedArgsLen(0..0, 1, 0..0, args.len()));
            }

            let first = args.remove(0);
            (
                Expression::String(format!(
                    "{:#?}",
                    typing::solve(vec![(Statement::Expression(first.clone()), first.1.clone())], interp, &interp.scope.clone())
                )),
                first.1.clone(),
            )
        }
        _ => return Err(InterpreterError::NoDirective(name)),
    })
}

#[derive(Clone, PartialEq, Debug)]
pub enum InterpreterError {
    MismatchedArgType(Span, Type, Span, Type),
    MismatchedType(Span, Type, Span, Type),
    MustBeType(Span, Type, Type),
    IndexOutOfBounds(Span, i64),
    MismatchedArgsLen(Span, usize, Span, usize),
    CantCall(Span, Type),
    CantDereferenced(Span, Type),
    CantFind(Span),
    NoDirective(String),
}

impl InterpreterError {
    pub fn format(self, s: String) -> String {
        use InterpreterError::*;

        match self {
            MismatchedArgType(lh, lht, rh, rht) => format!(
                "Mismatched types: {} takes something of type {} while {} is of type {}",
                &s[lh], lht, &s[rh], rht
            ),
            MismatchedType(lh, lht, rh, rht) => format!(
                "Mismatched type: '{}' is of type {} while '{}' is of type {}",
                &s[lh], lht, &s[rh], rht
            ),
            MustBeType(r, c, u) => {
                format!("{} must be of type {} but it is of type {}", &s[r], c, u)
            }
            IndexOutOfBounds(r, i) => format!("Index out of bounds {} is {}", &s[r], i),
            MismatchedArgsLen(id1, len1, id2, len2) => format!(
                "Mismatched number of arguments: {} expected {} while {} provided {}",
                &s[id1], len1, &s[id2], len2
            ),
            CantDereferenced(x, t) => {
                format!(
                    "{} of type {} can't be dereferenced only references can be",
                    &s[x], t
                )
            }
            // CantCall(x) => format!("{} can't be called", &s[x]),
            CantCall(_, t) => format!("Can't call of type {}", t),
            CantFind(x) => format!("Can't find variable named {}", &s[x]),
            NoDirective(x) => format!("No directive with name '{}'", x),
        }
    }
}

#[derive(Clone)]
pub enum Object {
    Integer(i64),
    Text(String),
    Boolean(bool),
    Range(i64, i64),
    // NOTE: Maybe these whould be refs to objects
    List(Vec<Arc<Mutex<Self>>>),
    Reference(Arc<Mutex<Self>>),
    ExternalFunction(
        Type,
        Arc<dyn Fn(Vec<Object>, &mut Interpreter) -> Object + Sync + Send>,
    ),
    InternalFunction(Type, Vec<String>, Expression<Metadata>),
    Nothing,
}

impl Object {
    fn type_(&self) -> Type {
        use Object::*;

        match self {
            Integer(_) => Type::integer(),
            Text(_) => Type::text(),
            Boolean(_) => Type::boolean(),
            Range(..) => Type::range(),
            List(i) => Type::list(
                i.get(0)
                    .map(|x| x.lock().unwrap().type_())
                    .unwrap_or(Type::Unknown(0, None)),
            ),
            Reference(x) => Type::reference(x.lock().unwrap().type_()),
            ExternalFunction(t, _) | InternalFunction(t, _, _) => t.clone(),
            Nothing => Type::nothing(),
        }
    }

    fn text(self) -> String {
        match self {
            Self::Text(x) => x,
            _ => panic!("Objects is not of type Integer"),
        }
    }

    fn integer(&self) -> i64 {
        match self {
            Self::Integer(x) => *x,
            _ => panic!("Objects is not of type Integer"),
        }
    }

    fn boolean(&self) -> bool {
        match self {
            Self::Boolean(x) => *x,
            _ => panic!("Objects is not of type Boolean"),
        }
    }

    fn negate(self) -> Self {
        match self {
            Self::Boolean(x) => Self::Boolean(!x),
            _ => panic!("Objects is not of type Boolean"),
        }
    }

    fn list(self) -> Vec<Arc<Mutex<Object>>> {
        match self {
            Self::List(x) => x,
            _ => panic!("Object is not of type List"),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(x) => write!(f, "{}", x),
            Self::Text(x) => write!(f, "\"{}\"", x),
            Self::Boolean(x) => write!(f, "{}", x),
            Self::Range(from, to) => write!(f, "{}:{}", from, to),
            Self::List(x) => write!(
                f,
                "[{}]",
                x.map_ref(|x| x.lock().unwrap().to_string()).join(", ")
            ),
            Self::Reference(x) => write!(f, "&{}", x.lock().unwrap()),
            Self::ExternalFunction(t, _) => write!(f, "{}", t),
            // Self::InternalFunction(t, _, _) => write!(f, "{}", t),
            Self::InternalFunction(t, _, _) => write!(f, "{}", t),
            Self::Nothing => write!(f, "Nothing"),
        }
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[wasm_bindgen]
#[derive(Debug, Clone)]
pub struct Interpreter {
    scope: HashMap<String, (Type, Arc<Mutex<Object>>)>,
}

fn add_func(
    map: &mut HashMap<String, (Type, Arc<Mutex<Object>>)>,
    name: &str,
    t: Type,
    f: fn(Vec<Object>, &mut Interpreter) -> Object,
) {
    map.insert(
        name.to_string(),
        (
            t.clone(),
            Arc::new(Mutex::new(Object::ExternalFunction(t, Arc::new(f)))),
        ),
    );
}

fn print(mut objs: Vec<Object>, _: &mut Interpreter) -> Object {
    crate::println(&format!("{}", objs.remove(0).text()));
    Object::Nothing
}

fn get_input(mut objs: Vec<Object>, _: &mut Interpreter) -> Object {
    Object::Text(crate::get_input(&objs.remove(0).text()))
}

fn add(objs: Vec<Object>, _: &mut Interpreter) -> Object {
    use Object::*;

    match (objs.get(0).unwrap(), objs.get(1).unwrap()) {
        (Integer(x), Integer(y)) => Integer(x + y),
        (Text(x), Text(y)) => Text(x.clone() + y),
        (List(x), List(y)) => {
            let mut x = x.clone();
            x.append(&mut y.clone());
            List(x.to_vec())
        }
        (a, b) => panic!(
            "print called with wrong types {} and {}",
            a.type_(),
            b.type_()
        ),
        // _ => unreachable!(),
    }
}

fn plot(objs: Vec<Object>, interp: &mut Interpreter) -> Object {
    crate::plot(&|x| {
        interp
            .clone()
            .call(objs[0].clone(), vec![Object::Integer(x)])
            .unwrap()
            .integer()
    });
    Object::Nothing
}

fn equal(objs: Vec<Object>, _: &mut Interpreter) -> Object {
    use Object::*;

    Object::Boolean(match (objs.get(0).unwrap(), objs.get(1).unwrap()) {
        (Integer(x), Integer(y)) => x == y,
        (Text(x), Text(y)) => x == y,
        (Boolean(x), Boolean(y)) => x == y,
        (Reference(x), Reference(y)) => Arc::ptr_eq(x, y),
        (ExternalFunction(_, x), ExternalFunction(_, y)) => Arc::ptr_eq(x, y),
        (InternalFunction(t1, a1, e1), InternalFunction(t2, a2, e2)) => {
            t1 == t2 && a1 == a2 && e1 == e2
        }
        (Nothing, Nothing) => true,
        _ => false,
    })
}

#[wasm_bindgen]
impl Interpreter {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Interpreter {
        let mut scope = HashMap::new();

        add_func(
            &mut scope,
            "print",
            Type::function(vec![Type::text(), Type::nothing()]),
            print,
        );

        add_func(
            &mut scope,
            "plot",
            Type::function(vec![
                Type::function(vec![Type::integer(), Type::integer()]),
                Type::nothing(),
            ]),
            plot,
        );

        add_func(
            &mut scope,
            "prompt",
            Type::function(vec![Type::text(), Type::text()]),
            get_input,
        );

        let list_or_string =
            Type::bounded(0, vec![Type::text(), Type::list(Type::Unknown(1, None))]);

        add_func(
            &mut scope,
            "len",
            Type::function(vec![list_or_string, Type::integer()]),
            |objs, _| match &objs[0] {
                Object::List(x) => Object::Integer(x.len() as i64),
                Object::Text(x) => Object::Integer(x.len() as i64),
                _ => unreachable!(),
            },
        );

        let operateable = Type::bounded(
            0,
            vec![
                Type::integer(),
                Type::text(),
                Type::list(Type::Unknown(1, None)),
            ],
        );

        add_func(
            &mut scope,
            "add",
            Type::function(vec![
                operateable.clone(),
                operateable.clone(),
                operateable.clone(),
            ]),
            add,
        );

        add_func(
            &mut scope,
            "+",
            Type::function(vec![
                operateable.clone(),
                operateable.clone(),
                operateable.clone(),
            ]),
            add,
        );

        let num_t = Type::integer();

        add_func(
            &mut scope,
            "*",
            Type::function(vec![num_t.clone(), num_t.clone(), num_t.clone()]),
            |objs, _| Object::Integer(objs[0].integer() * objs[1].integer()),
        );

        add_func(
            &mut scope,
            "-",
            Type::function(vec![num_t.clone(), num_t.clone(), num_t.clone()]),
            |objs, _| Object::Integer(objs[0].integer() - objs[1].integer()),
        );

        add_func(
            &mut scope,
            "/",
            Type::function(vec![num_t.clone(), num_t.clone(), num_t.clone()]),
            |objs, _| Object::Integer(objs[0].integer() / objs[1].integer()),
        );

        add_func(
            &mut scope,
            "<",
            Type::function(vec![num_t.clone(), num_t.clone(), Type::boolean()]),
            |objs, _| Object::Boolean(objs[0].integer() < objs[1].integer()),
        );

        add_func(
            &mut scope,
            ">",
            Type::function(vec![num_t.clone(), num_t.clone(), Type::boolean()]),
            |objs, _| Object::Boolean(objs[0].integer() > objs[1].integer()),
        );

        add_func(
            &mut scope,
            "==",
            Type::function(vec![Type::generic(0), Type::generic(0), Type::boolean()]),
            equal,
        );

        add_func(
            &mut scope,
            "!=",
            Type::function(vec![Type::generic(0), Type::generic(0), Type::boolean()]),
            |objs, i| equal(objs, i).negate(),
        );

        Interpreter { scope }
    }

    pub fn run_and_format(&mut self, line: &str) -> std::result::Result<String, String> {
        let parser = parser();

        if let Some(out) = crate::parser::tokenize(line.chars().peekable()) {
            if out.len() < 1 {
                return Ok(String::new());
            }

            let stream = chumsky::Stream::from_iter(out.last().unwrap().1.clone(), out.into_iter());
            match parser.parse(stream) {
                Ok(tree) => match typing::solve(tree, self, &self.scope.clone()) {
                    Ok(tree) => match self.run(&tree[0]) {
                        Ok(x) => match x {
                            Object::Nothing => Ok(String::new()),
                            a => Ok(format!("{}", a)),
                        },
                        Err(x) => Err(format!("{}", x.format(line.to_string()))),
                    },
                    Err(x) => Err(format!("{}", x.format(line.to_string()))),
                },
                Err(errors) => {
                    let mut s = String::new();

                    for err in errors {
                        s.push_str(&format!("{}", err))
                    }

                    Err(s)
                }
            }
        } else {
            Err(format!("Tokenizing string"))
        }
    }

    pub fn test_and_format(&mut self, line: &str) -> std::result::Result<(), String> {
        let parser = parser();

        if let Some(out) = crate::parser::tokenize(line.chars().peekable()) {
            if out.len() < 1 {
                return Ok(());
            }

            let stream = chumsky::Stream::from_iter(out.last().unwrap().1.clone(), out.into_iter());
            match parser.parse(stream) {
                Ok(tree) => match typing::solve(tree, self, &self.scope.clone()) {
                    Ok(_) => Ok(()),
                    Err(x) => Err(x.format(line.to_string())),
                },
                Err(errors) => {
                    let mut s = String::new();

                    for err in errors {
                        s.push_str(&format!("{}", err))
                    }

                    Err(s)
                }
            }
        } else {
            Err(format!("Tokenizing string"))
        }
    }
}

impl Interpreter {
    pub fn evaluate(&mut self, e: &(Expression<Metadata>, Metadata)) -> ParserResult<Object> {
        use Expression::*;

        Ok(match &e.0 {
            Literal(a) => Object::Integer(*a),
            String(a) => Object::Text(a.clone()),
            Boolean(a) => Object::Boolean(*a),
            Identifier(a) => self
                .scope
                .get(a)
                .ok_or(InterpreterError::CantFind(e.1 .0.clone()))?
                .1
                .lock()
                .unwrap()
                .clone(),
            Range(from, to) => {
                Object::Range(self.evaluate(from)?.integer(), self.evaluate(to)?.integer())
            }
            Call(func, args) => match self.evaluate(func)? {
                Object::ExternalFunction(_, func) => func(
                    args.iter()
                        .map(|e| self.evaluate(e))
                        .collect::<ParserResult<Vec<_>>>()?,
                    self,
                ),
                Object::InternalFunction(t, names, func) => {
                    let mut new_scope = self.scope.clone();
                    let args = args
                        .iter()
                        .map(|e| Ok((self.evaluate(e)?, e.1.1.clone())))
                        .collect::<ParserResult<Vec<_>>>()?;

                    for (name, arg) in names.iter().zip(args) {
                        new_scope.insert(name.clone(), (arg.1, Arc::new(Mutex::new(arg.0))));
                    }

                    let mut new_interp = Interpreter { scope: new_scope };
                    new_interp.evaluate(&(func, (0..0, t)))?
                }
                obj => return Err(InterpreterError::CantCall(func.1 .0.clone(), obj.type_())),
            },
            Lambda(args, body) => {
                Object::InternalFunction(e.1.1.clone(), args.clone(), body.0.clone())
            }
            Dereference(x) => match self.evaluate(x)? {
                Object::Reference(x) => x.lock().unwrap().clone(),
                _ => unreachable!(),
            },
            Reference(x) => Object::Reference(self.evaluate_ref(x)?),
            If(pred, body, else_) => {
                // TODO: Create own scope
                let is_true = self.evaluate(pred)?;
                if is_true.boolean() {
                    self.clone().run_list(body)?
                } else {
                    if let Some(else_) = else_ {
                        self.clone().run_list(else_)?
                    } else {
                        Object::Nothing
                    }
                }
            }
            List(items) => {
                let items = items
                    .iter()
                    .map(|x| self.evaluate(x).map(|x| Arc::new(Mutex::new(x))))
                    .collect::<ParserResult<Vec<_>>>()?;
                Object::List(items)
            }
            ListIndex(l, i) => {
                let list = self.evaluate(l)?;
                let idx = self.evaluate(i)?;

                match list {
                    Object::List(x) => match idx {
                        Object::Integer(idx) => x
                            .get(idx as usize)
                            .ok_or(InterpreterError::IndexOutOfBounds(i.1 .0.clone(), idx))?
                            .lock()
                            .unwrap()
                            .clone(),
                        Object::Range(from, to) => Object::List(
                            x.get(from as usize..to as usize)
                                .ok_or(InterpreterError::IndexOutOfBounds(i.1 .0.clone(), to))?
                                .to_vec(),
                        ),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            }
            DoList(statements) => self.clone().run_list(statements)?,
            Directive(..) => unreachable!(),
        })
    }

    pub fn call(&mut self, obj: Object, args: Vec<Object>) -> ParserResult<Object> {
        Ok(match obj {
            Object::ExternalFunction(_, func) => func(args, self),
            Object::InternalFunction(t, names, func) => {
                let mut new_scope = self.scope.clone();

                for (name, arg) in names.iter().zip(args) {
                    new_scope.insert(name.clone(), (arg.type_(), Arc::new(Mutex::new(arg))));
                }

                let mut new_interp = Interpreter { scope: new_scope };
                new_interp.evaluate(&(func, (0..0, t)))?
            }
            _ => unreachable!(),
        })
    }

    pub fn evaluate_ref(
        &mut self,
        e: &(Expression<Metadata>, Metadata),
    ) -> ParserResult<Arc<Mutex<Object>>> {
        use Expression::*;

        Ok(match &e.0 {
            Identifier(a) => self
                .scope
                .get(a)
                .ok_or(InterpreterError::CantFind(e.1 .0.clone()))?
                .1
                .clone(),
            Dereference(x) => match self.evaluate(x)? {
                Object::Reference(x) => x.clone(),
                _ => unreachable!(),
            },
            ListIndex(l, i) => {
                let list = self.evaluate(l)?;
                let idx = self.evaluate(i)?;

                match list {
                    Object::List(x) => x
                        .get(idx.integer() as usize)
                        .ok_or(InterpreterError::IndexOutOfBounds(
                            i.1 .0.clone(),
                            idx.integer(),
                        ))?
                        .clone(),
                    _ => unreachable!(),
                }
            }
            _ => Arc::new(Mutex::new(self.evaluate(e)?)),
        })
    }

    pub fn run_list(
        &mut self,
        statements: &Vec<(Statement<Metadata>, Metadata)>,
    ) -> ParserResult<Object> {
        Ok(statements
            .iter()
            .map(|s| self.run(s))
            .collect::<ParserResult<Vec<Object>>>()?
            .into_iter()
            .last()
            .unwrap())
    }

    pub fn run(&mut self, tree: &(Statement<Metadata>, Metadata)) -> ParserResult<Object> {
        match &tree.0 {
            Statement::Expression(x) => self.evaluate(x),
            Statement::Assignment(name, args, e) => {
                if let Some(args) = args {
                    let t = e.1.1.clone();

                    let obj = Object::InternalFunction(t.clone(), args.clone(), e.0.clone());

                    self.scope
                        .insert(name.clone(), (t, Arc::new(Mutex::new(obj))));
                } else {
                    let obj = self.evaluate(e)?;
                    self.scope
                        .insert(name.clone(), (e.1.1.clone(), Arc::new(Mutex::new(obj))));
                }
                Ok(Object::Nothing)
            }
            Statement::Reassignment(at, to) => {
                let val = self.evaluate(to)?;
                let obj = self.evaluate_ref(at)?;

                // if obj.lock().unwrap().type_() != val.type_() {
                //     return Err(InterpreterError::MismatchedType(
                //         at.1 .0.clone(),
                //         obj.lock().unwrap().type_(),
                //         to.1 .0.clone(),
                //         val.type_(),
                //     ));
                // }

                *obj.lock().unwrap() = val;
                Ok(Object::Nothing)
            }
            Statement::ForLoop(id, arr, body) => {
                let mut new_scope = self.scope.clone();
                let arr = self.evaluate(arr)?.list();

                for item in arr {
                    let item_t = item.lock().unwrap().type_();
                    new_scope.insert(id.clone(), (item_t, item));

                    let mut new_interp = Interpreter {
                        scope: new_scope.clone(),
                    };
                    new_interp.run_list(body)?;
                }

                Ok(Object::Nothing)
            }
        }
    }
}
