# Toybox

Toybox is still in a very very experimental stage right now, but the ultimate
goal is too have make programming language that make it easy for beginners to
learn to program.

## Running and Installing

This requires Rust and Cargo to be installed.

There two ways to interact with Toybox: though the web and though the terminal.
To run though the terminal run `cargo run --bin toybox --release
--features=build-binary` if you wish to run in web using WASM run `wasm-pack
build -d web/pkg --target web` then move to the `web/` directory and start an
HTTP server and open it in the browser.

## Examples

```
let a = 1
let b = 2
a + b
```

```
let shopping_list = ["Eggs", "Milk", "Bread"]
print(shopping_list[0])
```

```
let f(x) = x * x
f(5)
```
