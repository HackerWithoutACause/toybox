use std::fmt;
use std::iter::Peekable;

use chumsky::prelude::*;

use crate::vec_map::MapInVec;

pub trait Parser<T> = chumsky::Parser<Token, T, Error = Simple<Token>>;
pub trait FinalParser = Parser<(Statement<Span>, Span)>;
pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Special {
    Assign,
    Equal,
    NotEqual,
    Plus,
    Minus,
    Dot,
    Asterisk,
    Slash,
    OpenParentheses,
    CloseParentheses,
    OpenBracket,
    CloseBracket,
    Comma,
    Ampersand,
    Colon,
    Arrow,
    LessThen,
    GreaterThen,
    Dollar,
}

impl fmt::Display for Special {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Special::*;

        write!(
            f,
            "{}",
            match self {
                Assign => "=",
                Equal => "==",
                NotEqual => "!=",
                Plus => "+",
                Minus => "-",
                Dot => ".",
                Asterisk => "*",
                Slash => "/",
                OpenParentheses => "(",
                CloseParentheses => ")",
                OpenBracket => "[",
                CloseBracket => "]",
                Comma => ",",
                Ampersand => "&",
                Colon => ":",
                Arrow => "->",
                LessThen => "<",
                GreaterThen => ">",
                Dollar => "$",
            }
        )
    }
}

impl Special {
    fn is_special(ch: char) -> bool {
        "=!+-.*/(),&:[]<>$".contains(ch)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    String(String),
    Number(i64),
    Identifier(String),
    Special(Special),
    While,
    Do,
    End,
    If,
    Then,
    Def,
    For,
    Let,
    True,
    False,
    Else,
    In,
}

impl Token {
    pub fn to_identifier<M>(self) -> Expression<M> {
        Expression::Identifier(match self {
            Token::Special(x) => x.to_string(),
            Token::Identifier(x) => x,
            _ => panic!("Tried ot identify wrong token type"),
        })
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::String(x) => write!(f, "\x1B[1;32m\"{}\"\x1B[0m", x),
            Token::Number(x) => write!(f, "\x1B[1;34m{}\x1B[0m", x),
            Token::Identifier(x) => write!(f, "\x1B[1;31m{}\x1B[0m", x),
            Token::Special(x) => write!(f, "{}", x),
            Token::While => write!(f, "while"),
            Token::Then => write!(f, "then"),
            Token::Do => write!(f, "do"),
            Token::End => write!(f, "end"),
            Token::If => write!(f, "if"),
            Token::Def => write!(f, "def"),
            Token::For => write!(f, "for"),
            Token::Else => write!(f, "else"),
            Token::Let => write!(f, "let"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::In => write!(f, "in"),
        }
    }
}

pub fn tokenize<I: Iterator<Item = char>>(mut input: Peekable<I>) -> Option<Vec<(Token, Span)>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut span = 0..0;

    while let Some(ch) = input.next() {
        match ch {
            '"' => {
                span.start = span.end;
                let mut succ = false;
                while let Some(ch) = input.next() {
                    span.end += 1;
                    if ch == '"' {
                        succ = true;
                        span.end += 1;
                        let old = std::mem::replace(&mut current, String::new());
                        tokens.push((Token::String(old), span.clone()));
                        break;
                    }
                    current.push(ch);
                }

                if !succ {
                    return None;
                }
            }
            c if c.is_alphabetic() || c == '_' => {
                span.start = span.end;
                current.push(c);

                while let Some(ch) = input.peek() {
                    if ch.is_alphanumeric() || *ch == '_' {
                        span.end += 1;
                        current.push(input.next().unwrap())
                    } else {
                        break;
                    }
                }

                span.end += 1;

                let old = std::mem::replace(&mut current, String::new());
                tokens.push((
                    match old.to_lowercase().as_str() {
                        "while" => Token::While,
                        "do" => Token::Do,
                        "end" => Token::End,
                        "if" => Token::If,
                        "then" => Token::Then,
                        "def" => Token::Def,
                        "for" => Token::For,
                        "let" => Token::Let,
                        "else" => Token::Else,
                        "false" => Token::False,
                        "true" => Token::True,
                        "in" => Token::In,
                        _ => Token::Identifier(old),
                    },
                    span.clone(),
                ));
            }
            c if c.is_whitespace() => span.end += 1,
            c if c.is_digit(10) => {
                span.start = span.end;
                current.push(c);

                while let Some(ch) = input.peek() {
                    if ch.is_digit(10) {
                        span.end += 1;
                        current.push(input.next().unwrap())
                    } else {
                        break;
                    }
                }

                span.end += 1;

                let old = std::mem::replace(&mut current, String::new());
                tokens.push((Token::Number(old.parse().ok()?), span.clone()));
            }
            c if Special::is_special(c) => {
                span.start = span.end;
                current.push(c);

                while let Some(ch) = input.peek() {
                    if *ch == '=' || *ch == '>' {
                        span.end += 1;
                        current.push(input.next().unwrap())
                    } else {
                        break;
                    }
                }

                span.end += 1;

                let old = std::mem::replace(&mut current, String::new());
                use Special::*;
                tokens.push((
                    Token::Special(match old.to_lowercase().as_str() {
                        "=" => Assign,
                        "==" => Equal,
                        "!=" => NotEqual,
                        "+" => Plus,
                        "-" => Minus,
                        "." => Dot,
                        "*" => Asterisk,
                        "/" => Slash,
                        "(" => OpenParentheses,
                        ")" => CloseParentheses,
                        "," => Comma,
                        "&" => Ampersand,
                        ":" => Colon,
                        "->" => Arrow,
                        "[" => OpenBracket,
                        "]" => CloseBracket,
                        "<" => LessThen,
                        ">" => GreaterThen,
                        "$" => Dollar,
                        _ => return None,
                    }),
                    span.clone(),
                ));
            }
            _ => {
                // eprintln!("Error: Unknown character: '{}'", ch);
                return None;
            }
        }
    }

    return Some(tokens);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<M> {
    Literal(i64),
    Identifier(String),
    Boolean(bool),
    List(Vec<(Self, M)>),
    Call(Box<(Self, M)>, Vec<(Self, M)>),
    String(String),
    Lambda(Vec<String>, Box<(Self, M)>),
    Reference(Box<(Self, M)>),
    Dereference(Box<(Self, M)>),
    ListIndex(Box<(Self, M)>, Box<(Self, M)>),
    Range(Box<(Self, M)>, Box<(Self, M)>),
    If(
        Box<(Self, M)>,
        Vec<(Statement<M>, M)>,
        Option<Vec<(Statement<M>, M)>>,
    ),
    DoList(Vec<(Statement<M>, M)>),
    Directive(String, Vec<(Self, M)>),
}

impl<M> fmt::Display for Expression<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Expression::Operation(op, lh, rh) => write!(f, "{} {} {}", lh.0, op, rh.0),
            Expression::Literal(x) => write!(f, "{}", x),
            Expression::String(x) => write!(f, "\"{}\"", x),
            Expression::Identifier(x) => write!(f, "{}", x),
            Expression::Boolean(x) => write!(f, "{}", x),
            Expression::List(items) => write!(f, "[{}]", Expression::list(&items, ", ")),
            Expression::Call(id, args) => {
                write!(f, "{} ( {} )", id.0, Expression::list(args, ", "))
            }
            Expression::ListIndex(l, i) => write!(f, "{}[{}]", l.0, i.0),
            Expression::Lambda(args, expr) => write!(f, "({}) -> {}", args.join(", "), expr.0),
            Expression::Reference(x) => write!(f, "&{}", x.0),
            Expression::Dereference(x) => write!(f, "*{}", x.0),
            Expression::If(pred, expr, else_) => match else_ {
                Some(else_) => write!(
                    f,
                    "if {} then {} else {} end",
                    pred.0,
                    expr.map_ref(|(s, _)| s.to_string()).join(" "),
                    else_.map_ref(|(s, _)| s.to_string()).join(" ")
                ),
                None => write!(
                    f,
                    "if {} then {} end",
                    pred.0,
                    expr.map_ref(|(s, _)| s.to_string()).join(" ")
                ),
            },
            _ => todo!(),
            // Expression::Reference(x) => write!(f, "&{}", x.0),
            // Expression::Dereference(x) => write!(f, "*{}", x.0),
        }
    }
}

impl<M> Expression<M> {
    pub fn string(self) -> Option<String> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    fn list(list: &Vec<(Self, M)>, dim: &str) -> String {
        let mut str = String::new();
        let mut list = list.iter().peekable();

        while let Some(item) = list.next() {
            str.push_str(&item.0.to_string());

            if list.peek().is_some() {
                str.push_str(dim);
            }
        }

        str
    }
}

fn identifier() -> impl Parser<String> + Clone {
    filter_map(|span, x| match x {
        Token::Identifier(x) => Ok(x),
        _ => Err(Simple::expected_input_found(span, Vec::new(), Some(x))),
    })
}

fn fold_operation(
    lhs: (Expression<Span>, Span),
    (op, rhs): ((Token, Span), (Expression<Span>, Span)),
) -> (Expression<Span>, Span) {
    let span = lhs.1.start..rhs.1.end;
    (
        Expression::Call(Box::new((op.0.to_identifier(), op.1)), vec![lhs, rhs]),
        span,
    )
}

fn identifier_list() -> impl Parser<(Vec<String>, Span)> + Clone {
    identifier()
        .clone()
        .chain(
            just(Token::Special(Special::Comma))
                .ignore_then(identifier().clone())
                .repeated(),
        )
        .then_ignore(just(Token::Special(Special::Comma)).or_not())
        .or_not()
        .map_with_span(|item, span| (item.unwrap_or_else(Vec::new), span))
}

fn expression(
    statement: impl Parser<(Statement<Span>, Span)> + Clone + 'static,
) -> impl Parser<(Expression<Span>, Span)> + Clone {
    recursive(|expr| {
        let items = expr
            .clone()
            .chain(
                just(Token::Special(Special::Comma))
                    .ignore_then(expr.clone())
                    .repeated(),
            )
            .then_ignore(just(Token::Special(Special::Comma)).or_not())
            .or_not()
            .map(|item| item.unwrap_or_else(Vec::new));

        let atom = choice((
            filter_map(|span: Span, x| match x {
                Token::Number(x) => Ok(Expression::Literal(x)),
                Token::Identifier(x) => Ok(Expression::Identifier(x)),
                Token::String(x) => Ok(Expression::String(x)),
                Token::True => Ok(Expression::Boolean(true)),
                Token::False => Ok(Expression::Boolean(false)),
                _ => Err(Simple::expected_input_found(span, Vec::new(), Some(x))),
            })
            .map_with_span(|expr, span| (expr, span)),
            just(Token::Special(Special::OpenParentheses))
                .ignore_then(identifier_list())
                .then_ignore(just(Token::Special(Special::CloseParentheses)))
                .then_ignore(just(Token::Special(Special::Arrow)))
                .then(expr.clone())
                .map_with_span(|(a, e), span| (Expression::Lambda(a.0, Box::new(e)), span)),
            expr.clone().delimited_by(
                just(Token::Special(Special::OpenParentheses)),
                just(Token::Special(Special::CloseParentheses)),
            ),
            items
                .clone()
                .delimited_by(
                    just(Token::Special(Special::OpenBracket)),
                    just(Token::Special(Special::CloseBracket)),
                )
                .map_with_span(|items, span| (Expression::List(items), span)),
            just(Token::Special(Special::Dollar))
                .ignore_then(identifier())
                .then(items.clone().delimited_by(
                    just(Token::Special(Special::OpenParentheses)),
                    just(Token::Special(Special::CloseParentheses)),
                ))
                .map_with_span(|(name, args), span| (Expression::Directive(name, args), span)),
        ));

        let if_ = just(Token::If)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Then))
            .then(statement.clone().repeated())
            .then(
                just(Token::Else)
                    .ignore_then(statement.clone().repeated())
                    .or_not(),
            )
            .then_ignore(just(Token::End))
            .map_with_span(|((pred, expr), else_), span| {
                (Expression::If(Box::new(pred), expr, else_), span)
            });

        let do_ = just(Token::Do)
            .ignore_then(statement.clone().repeated())
            .then_ignore(just(Token::End))
            .map_with_span(|statements, span| (Expression::DoList(statements), span));

        let call = choice((if_, do_, atom))
            .then(
                items
                    .delimited_by(
                        just(Token::Special(Special::OpenParentheses)),
                        just(Token::Special(Special::CloseParentheses)),
                    )
                    .map_with_span(|args, span| (args, span))
                    .repeated(),
            )
            .foldl(|f, args| {
                let span = f.1.start..args.1.end;
                (Expression::Call(Box::new(f), args.0), span)
            });

        let list_index = call
            .then(
                just(Token::Special(Special::OpenBracket))
                    .ignore_then(expr.clone())
                    .then_ignore(just(Token::Special(Special::CloseBracket)))
                    .map_with_span(|x, s| (x, s))
                    .repeated(),
            )
            .foldl(|l, (i, span)| (Expression::ListIndex(Box::new(l), Box::new(i)), span));

        let op = |c| just(Token::Special(c)).map_with_span(|op, span| (op, span));

        let reference = op(Special::Ampersand)
            .repeated()
            .then(list_index)
            .foldr(|op, rhs| {
                let span = op.1.start..rhs.1.end;
                (Expression::Reference(Box::new(rhs)), span)
            });

        let dereference = op(Special::Asterisk)
            .repeated()
            .then(reference)
            .foldr(|op, rhs| {
                let span = op.1.start..rhs.1.end;
                (Expression::Dereference(Box::new(rhs)), span)
            });

        let range = dereference
            .clone()
            .then(
                just(Token::Special(Special::Colon))
                    .ignore_then(dereference)
                    .map_with_span(|x, s| (s, x))
                    .repeated(),
            )
            .foldl(|lh, (span, rh)| (Expression::Range(Box::new(lh), Box::new(rh)), span));

        let product = range
            .clone()
            .then(
                op(Special::Asterisk)
                    .or(op(Special::Slash))
                    .then(range)
                    .repeated(),
            )
            .foldl(fold_operation);

        let sum = product
            .clone()
            .then(
                op(Special::Plus)
                    .or(op(Special::Minus))
                    .then(product)
                    .repeated(),
            )
            .foldl(fold_operation);

        let equality = sum
            .clone()
            .then(
                op(Special::Equal)
                    .or(op(Special::NotEqual))
                    .or(op(Special::GreaterThen))
                    .or(op(Special::LessThen))
                    .then(sum)
                    .repeated(),
            )
            .foldl(fold_operation);

        equality
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement<M> {
    Expression((Expression<M>, M)),
    Assignment(String, Option<Vec<String>>, (Expression<M>, M)),
    Reassignment((Expression<M>, M), (Expression<M>, M)),
    ForLoop(String, (Expression<M>, M), Vec<(Self, M)>),
}

impl<M> fmt::Display for Statement<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::Expression(e) => write!(f, "{}", e.0),
            Statement::Assignment(i, a, e) => {
                if let Some(a) = a {
                    write!(f, "let {}({}) = {}", i, a.join(", "), e.0)
                } else {
                    write!(f, "let {} = {}", i, e.0)
                }
            }
            Statement::Reassignment(x, b) => write!(f, "{} = {}", x.0, b.0),
            _ => todo!(),
        }
    }
}

fn statement() -> impl Parser<(Statement<Span>, Span)> {
    recursive(|statement| {
        let expr = expression(statement.clone());

        choice((
            just(Token::Let)
                // .ignore_then(let_identifier())
                .ignore_then(identifier())
                .then(
                    just(Token::Special(Special::OpenParentheses))
                        .ignore_then(identifier_list())
                        .then_ignore(just(Token::Special(Special::CloseParentheses)))
                        .or_not(),
                )
                .then_ignore(just(Token::Special(Special::Assign)))
                .then(expr.clone())
                .map_with_span(|((a, args), b), span| {
                    (Statement::Assignment(a, args.map(|x| x.0), b), span)
                }),
            just(Token::Def)
                .ignore_then(identifier())
                .then(
                    just(Token::Special(Special::OpenParentheses))
                        .ignore_then(identifier_list())
                        .then_ignore(just(Token::Special(Special::CloseParentheses))),
                )
                .then_ignore(just(Token::Do))
                .then(statement.clone().repeated().map_with_span(|a, s| (a, s)))
                .then_ignore(just(Token::End))
                .map_with_span(|((a, args), b), span| {
                    (
                        Statement::Assignment(a, Some(args.0), (Expression::DoList(b.0), b.1)),
                        span,
                    )
                }),
            just(Token::For)
                .ignore_then(identifier())
                .then_ignore(just(Token::In))
                .then(expr.clone())
                .then_ignore(just(Token::Do))
                .then(statement.clone().repeated())
                .then_ignore(just(Token::End))
                .map_with_span(|((id, arr), body), span| (Statement::ForLoop(id, arr, body), span)),
            expr.clone()
                .then_ignore(just(Token::Special(Special::Assign)))
                .then(expr.clone())
                .map_with_span(|(a, b), span| (Statement::Reassignment(a, b), span)),
            expr.map_with_span(|x, span| (Statement::Expression(x), span)),
        ))
    })
}

pub fn parser() -> impl Parser<Vec<(Statement<Span>, Span)>> {
    statement().repeated().then_ignore(end())
}
