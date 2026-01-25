use vstd::invariant;
use vstd::math::max;
use vstd::prelude::*;

verus! {
    spec fn leftpad_spec(c: char, n: nat, s: Seq<char>) -> Seq<char>
        decreases n - s.len()
    {
        if s.len() >= n {
            s
        } else {
            let next = leftpad_spec(c,(n - 1) as nat, s);
            next.insert(0, c)
        }
    }

    proof fn leftpad_proof(c: char, n: nat, s: Seq<char>)
        ensures
            result_has_correct_length(leftpad_spec(c, n, s), n, s),
            prefix_is_only_padded_characters(c, n, s, leftpad_spec(c, n, s)),
            suffix_is_original_string(c, n, s, leftpad_spec(c, n, s)),
        decreases
            n - s.len()
    {
        if s.len() < n {
            leftpad_proof(c, (n - 1) as nat, s)
        } else { }
    }

    // The length of the output is max(n, len(str))
    spec fn result_has_correct_length(result: Seq<char>, n: nat, s: Seq<char>) -> bool {
        result.len() == max(n as int, s.len() as int)
    }

    // The prefix of the output is padding characters and nothing but padding characters
    spec fn prefix_is_only_padded_characters(c: char, n: nat, s: Seq<char>, result: Seq<char>) -> bool {
        let pad_len = max(n as int - s.len() as int, 0);
        forall|i: int| 0 <= i < pad_len ==> result[i] == c
    }

    // The suffix of the output is the original string.
    spec fn suffix_is_original_string(c: char, n: nat, s: Seq<char>, result: Seq<char>) -> bool {
        forall|i: int| 0 <= i < s.len() ==> result[max(n as int - s.len() as int, 0) + i] == s[i]
    }

    exec fn leftpad_impl(c: char, n: usize, s: Vec<char>) -> (result: Vec<char>)
        ensures
            result@ == leftpad_spec(c, n as nat, s@),
    {
        print_input(c, n, &s);
        let pad_length = n.saturating_sub(s.len());
        let mut idx = 0;
        let mut result = s;
        while idx < pad_length
            invariant
                0 <= idx <= pad_length,
                result@ == leftpad_spec(c, s@.len() + idx as nat, s@),
            decreases pad_length - idx
        {
            result.insert(0, c);
            idx = idx + 1;
        }
        print_output(&result);
        result
    }

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

    fn main() {
        proof {
            reveal_strlit("foo");
            reveal_strlit("!foo");
        }

        let input = vec!['f', 'o', 'o'];
        let zero_padding = leftpad_impl('!', 0, input);
        assert(zero_padding@ == "foo"@);

        let input = vec!['f', 'o', 'o'];
        let equal_padding = leftpad_impl('!', 3, input);
        assert(equal_padding@ == "foo"@);

        let input = vec!['f', 'o', 'o'];
        let some_padding = leftpad_impl('!', 4, input);
        assert(some_padding@ == "!foo"@)
    }
} // verus!
