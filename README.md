# Nuprl
## Building
### Dependencies
Before building, please ensure that [Rust Cargo](https://www.rust-lang.org) is installed
with rustc version >= 1.69.0.

### Building the standard library
The full `nuprl` executable embeds a compiled standard library. To do this yourself,
run the `build_stdlib.sh` script, which builds a stripped-back version of `nuprl` and uses
it to compile the standard library. The compiled library will be output as `std.nulib`.

### Building the interpreter
Once `std.nulib` has been created, run `cargo build --release`. The executable will be
placed at `target/release/nuprl`.
