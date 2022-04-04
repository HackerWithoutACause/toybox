#![feature(trait_alias)]
#![allow(dead_code)]

mod interpreter;
mod parser;
mod vec_map;

use std::cmp::min;
use std::io::{stdin, stdout, Stdout, Write};
use termion::event::{Event, Key};
use termion::input::TermRead;
use termion::raw::{IntoRawMode, RawTerminal};

use interpreter::Interpreter;

use crate::parser::Token;

struct Editor {
    stdout: RawTerminal<Stdout>,
    history: Vec<String>,
    interpreter: Interpreter,
}

impl Editor {
    pub fn new(interpreter: Interpreter) -> Self {
        let stdout = stdout().into_raw_mode().unwrap();

        Editor {
            history: Vec::new(),
            stdout,
            interpreter,
        }
    }

    fn highlight(line: String) -> String {
        if let Some(tokens) = parser::tokenize(line.chars().peekable()) {
            let mut highlighted = String::new();

            let mut last_end = 0;
            for token in tokens {
                highlighted.push_str(&line[last_end..token.1.start]);

                highlighted.push_str(match token.0 {
                    Token::String(_) => "\x1B[32m",
                    Token::Number(_) | Token::True | Token::False => "\x1B[35m",
                    Token::While
                    | Token::Do
                    | Token::End
                    | Token::If
                    | Token::Then
                    | Token::Def
                    | Token::For
                    | Token::Else
                    | Token::Let => "\x1B[33m",
                    _ => "",
                });

                highlighted.push_str(&line[token.1.start..token.1.end]);
                highlighted.push_str("\x1B[0m");
                last_end = token.1.end;
            }

            highlighted
        } else {
            line
        }
    }

    fn ghost(&mut self, line: &str) -> String {
        self.stdout.suspend_raw_mode().unwrap();

        let r = match self.interpreter.test_and_format(line) {
            Ok(..) => String::new(),
            Err(x) => format!("\x1B[31mError:\x1B[39m {}", x),
        };

        self.stdout.activate_raw_mode().unwrap();

        r
    }

    pub fn readline(&mut self) -> Option<String> {
        let mut lines = Vec::new();
        let mut line = String::new();
        let mut cursor: usize = 0;
        let mut history_pos: usize = self.history.len();
        self.stdout.activate_raw_mode().unwrap();

        print!("\r\x1B[2K>> {}", line);
        self.stdout.flush().unwrap();

        for c in stdin().events() {
            match c.unwrap() {
                Event::Key(Key::Char('\n')) => {
                    lines.push(line.clone());
                    self.history.push(line);
                    print!("\r\n");
                    break;
                }
                Event::Key(Key::Char('\t')) => {
                    line.insert_str(cursor, "    ");
                    cursor += 4;
                }
                Event::Key(Key::Alt('\r')) => {
                    lines.push(line.clone());
                    self.history.push(line);
                    line = String::new();
                    cursor = 0;
                    print!("\r\n");
                }
                Event::Key(Key::Backspace) => {
                    if cursor > 0 {
                        cursor = cursor.saturating_sub(1);
                        line.remove(cursor);
                    }
                }
                Event::Key(Key::Char(x)) => {
                    line.insert(cursor, x);
                    cursor += 1;
                }
                Event::Key(Key::Ctrl('c')) => {
                    print!("\r\n");
                    return None;
                }
                Event::Key(Key::Left) => cursor = cursor.saturating_sub(1),
                Event::Key(Key::Right) => cursor = min(line.len(), cursor + 1),
                Event::Key(Key::Up) => {
                    history_pos = history_pos.saturating_sub(1);
                    line = self
                        .history
                        .get(history_pos)
                        .map(String::clone)
                        .unwrap_or_default();
                    cursor = line.len();
                }
                Event::Key(Key::Down) => {
                    history_pos = min(self.history.len(), history_pos + 1);
                    line = self
                        .history
                        .get(history_pos)
                        .map(String::clone)
                        .unwrap_or_default();
                    cursor = line.len();
                }
                _ => (),
            }

            let indicator = match lines.is_empty() {
                true => ">>",
                false => "..",
            };

            print!(
                "\r\x1B[2K{} {}\n\r\x1B[2K\x1B[2m{}\x1B[0m\x1B[{}G\x1B[1A",
                indicator,
                Self::highlight(line.clone()),
                self.ghost(&(lines.join("\n") + &line)),
                cursor + 4
            );
            self.stdout.flush().unwrap();
        }

        print!("\r\x1B[2K\x1B[1A",);

        self.stdout.suspend_raw_mode().unwrap();

        Some(lines.join("\n"))
    }
}

fn println(msg: &str) {
    print!("{}\r\n", msg);
}

fn get_input(_: &str) -> String {
    String::new()
}

fn plot(_: &dyn Fn(i64) -> i64) {
    todo!()
}

fn main() {
    let mut editor = Editor::new(Interpreter::new());
    let mut interpreter = Interpreter::new();

    while let Some(line) = editor.readline() {
        if !line.is_empty() {
            print!("\r\n");
            // println!("{:?}", interpreter.run_and_format(&line, &parser()));
            match interpreter.run_and_format(&line) {
                Ok(x) if !x.is_empty() => {
                    println!("{}", x)
                }
                Err(x) => println!("\x1B[31mError:\x1B[0m {}", x),
                _ => (),
            }

            editor.interpreter = interpreter.clone();
        }
    }
}
