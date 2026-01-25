#![feature(proc_macro_hygiene)]
use vstd::{modes::*, prelude::*, seq::*, *};
use vstd::math::max;

#[verifier::external_body]
fn print_input(c: char, n: usize, s: &Vec<char>)
{
    println!();
    println!("Input: c={c}, n={n}, s={s:?}");
}


#[verifier::external_body]
fn print_output(result: &Vec<char>)
{
    println!("Output: result={result:?}");
    println!();
}

#[verus_spec(result =>
    ensures 
        result.len() == max(n as int, s.len() as int),
        forall|i: int| 0 <= i < max(n as int - s.len() as int, 0) ==> result[i] == c,
        forall|i: int| 0 <= i < s.len() ==> result[max(n as int - s.len() as int, 0) + i] == s[i]
)]
fn leftpad(c: char, n: usize, s: Vec<char>) -> Vec<char> {
    print_input(c, n, &s);
    let pad_length = n.saturating_sub(s.len());
    let mut idx = 0;
    let mut result = s;
    #[verus_spec(
        invariant 
            0 <= idx <= pad_length,
            result@.len() == s@.len() + idx,
            forall |j: int| 0 <= j < idx ==> result@[j] == c,
            forall |j: int| 0 <= j < s@.len() ==> result@[idx + j] == s[j],
        decreases pad_length - idx
    )]
    while idx < pad_length {
        result.insert(0, c);
        idx = idx + 1;
    }
    print_output(&result);
    result
}

fn main() {
    leftpad('!', 0, "foo".chars().collect());
    leftpad('!', 3, "foo".chars().collect());
    leftpad('!', 5, "foo".chars().collect());
}