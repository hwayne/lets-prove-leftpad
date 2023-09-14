#![feature(generic_const_exprs)]
#![feature(generic_arg_infer)]

#[derive(Clone, Copy)]
struct ConstLenString<const LEN: usize>([char; LEN]);

struct Repeated<const C: char, const R: usize>;

struct Padded<const P: usize, const C: char, const N: usize>(Repeated<C, P>, ConstLenString<N>);

trait LeftPad<const N: usize> {
    fn leftpad<const R: usize, const C: char>(self) -> Padded<{ max(R, N) - N }, C, N>;
}

impl<const N: usize> LeftPad<N> for ConstLenString<N> {
    fn leftpad<const R: usize, const C: char>(self) -> Padded<{ max(R, N) - N }, C, N> {
        Padded(Repeated, self)
    }
}

const fn max(a: usize, b: usize) -> usize {
    if a > b {
        a
    } else {
        b
    }
}

pub fn proven_by_compiler() {
    let to_pad = ConstLenString(['h', 'e', 'l', 'l', 'o']);

    let _padded: Padded<0, '!', 5> = to_pad.leftpad::<4, '!'>();
    let _padded: Padded<1, '!', 5> = to_pad.leftpad::<6, '!'>();
}
