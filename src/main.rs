use sat::{Lit, Prop, Solver};
mod sat;

use sat::ClauseBuilderHelper;
use Lit::*;

// Define a type representing a position in the Sudoku grid.
// 0 <= r, c < 9.
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Debug)]
struct GridCell {
    r: i32,
    c: i32,
}

/// We can define custom "propositions" (without interpretation) by addding an `impl Prop` for them.
/// The `Num(p, v)` proposition says that grid cell `p` contains the digit `v`.
#[derive(Copy, Clone, Eq, PartialEq, Debug, PartialOrd, Ord)]
struct Num(GridCell, i32);
impl Prop for Num {}

fn main() {
    // Create a new solver. All of the constraints will be added to this object.
    let mut s = Solver::new();

    // Set up the rules for Sudoku:
    let cells: Vec<GridCell> = (0..9)
        .flat_map(|r| (0..9).map(move |c| GridCell { r, c }))
        .collect();

    // Each cell has a value.
    for &p in &cells {
        // This means that exactly one of Num(p, 1); Num(p, 2); ...; Num(p, 9) is true.
        s.exactly_one((1..=9).map(|v| Pos(Num(p, v))));
    }

    // If two different cells share a row, column, or 3x3 box, they cannot have the same value.
    for &p1 in &cells {
        for &p2 in &cells {
            if p1 == p2 {
                continue;
            }
            if p1.r == p2.r || p1.c == p2.c || (p1.r / 3, p1.c / 3) == (p2.r / 3, p2.c / 3) {
                for v in 1..=9 {
                    // They cannot both be 'v':
                    s.at_most_one([Pos(Num(p1, v)), Pos(Num(p2, v))]);
                }
            }
        }
    }

    // Get the solution.
    // In production code, you should check here for errors (timeouts or unsatisfiability).
    let ans = s.solve_splr().expect("solvable").unwrap();

    // Print the resulting grid:
    for r in 0..9 {
        for c in 0..9 {
            let p = GridCell { r, c };
            for v in 1..=9 {
                // We can look up the `Var` for each proposition by calling `.resolve_prop`.
                if ans[&s.resolve_prop(Num(p, v))] {
                    print!("{v}");
                }
            }
        }
        println!();
    }
}
