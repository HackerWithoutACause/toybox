#![feature(trait_alias, once_cell)]
mod interpreter;
mod parser;
mod vec_map;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    // #[wasm_bindgen(method, js_name = print)]
    pub fn println(s: &str);
    pub fn get_input(s: &str) -> String;
    pub fn print_output(s: &str);
    pub fn print_error(s: &str);
    pub fn plot(f: &dyn Fn(i64) -> i64);
}
