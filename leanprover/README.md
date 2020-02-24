# [Lean](https://leanprover.github.io)

[Live proof demo][lpd]

[lpd]: https://leanprover.github.io/live/latest/#code=import%20data.nat.basic%0Aimport%20data.list%0Aopen%20list%0A%0Auniverses%20u%0Avariables%20%7B%CE%B1%20:%20Type%20u%7D%0A%0A@%5Bsimp%5D%20def%20leftpad%20(n%20:%20%E2%84%95)%20(a%20:%20%CE%B1)%20(l%20:%20list%20%CE%B1)%20:%20list%20%CE%B1%20:=%0Arepeat%20a%20(n%20-%20length%20l)%20++%20l%0A%0A#eval%20list.as_string%20(leftpad%205%20'b'%20(string.to_list%20%22ac%22))%0A%0Atheorem%20leftpad_length%20(n%20:%20%E2%84%95)%20(a%20:%20%CE%B1)%20(l%20:%20list%20%CE%B1)%20:%20%0Alength%20(leftpad%20n%20a%20l)%20=%20max%20n%20(length%20l)%20:=%0Abegin%0A%20%20simp,%0A%20%20rw%20%5Badd_comm,%20nat.sub_add_eq_max%5D%0Aend%0A%0Atheorem%20leftpad_prefix%20%5Bdecidable_eq%20%CE%B1%5D%20(n%20:%20%E2%84%95)%20(a%20:%20%CE%B1)%20(l%20:%20list%20%CE%B1)%20:%0A(repeat%20a%20(n%20-%20length%20l))%20%3C+:%20(leftpad%20n%20a%20l)%20:=%20by%20simp%0A%0Atheorem%20leftpad_suffix%20%5Bdecidable_eq%20%CE%B1%5D%20(n%20:%20%E2%84%95)%20(a%20:%20%CE%B1)%20(l%20:%20list%20%CE%B1)%20:%0Al%20%3C:+%20(leftpad%20n%20a%20l)%20:=%20by%20simp%0A

## About Lean

> Lean is an open source theorem prover and programming language being developed at Microsoft Research. 
> Lean aims to bridge the gap between interactive and automated theorem proving, by situating automated 
> tools and methods in a framework that supports user interaction and the construction of fully 
> specified axiomatic proofs.

> The Lean project was launched by Leonardo de Moura at Microsoft Research in 2013. It is an open source
> project, hosted on GitHub.

> Several users maintain the mathematical components library [mathlib] for Lean.

[mathlib]: https://github.com/leanprover-community/mathlib

Lean has an active community on [zulipchat](https://leanprover.zulipchat.com).

## About the proof

Lean has a very capable core prelude and the mathlib serves as a very capable standard library. 
Therefore, I implemented `leftpad` simply as

```lean
def leftpad (n : ℕ) (a : α) (l : list α) : list α :=
repeat a (n - length l) ++ l
```

A cool feature of Lean is its integration with the editor. Typing `\nat` then <kbd>space</kbd> would enter `ℕ`.

The `string` type in Lean is represented by `list char` in the type and proofs, even though it is implemented 
in the VM as a dynamic array. I therefore define leftpad in term of `list`.

The file proceeds to prove the three properties of leftpad presented by Hillel as three `theorem`s.

```lean
theorem leftpad_length (n : ℕ) (a : α) (l : list α) : 
length (leftpad n a l) = max n (length l) := <proof>

theorem leftpad_prefix [decidable_eq α] (n : ℕ) (a : α) (l : list α) :
(repeat a (n - length l)) <+: (leftpad n a l) := by {rw leftpad, simp}

theorem leftpad_suffix [decidable_eq α] (n : ℕ) (a : α) (l : list α) :
l <:+ (leftpad n a l) := by {rw leftpad, simp}
```

`by {rw leftpad, simp}` is proving the theorems using tactics. 
Tactic mode is one of Lean's central features. 
It is in tactic mode that Lean displays a view of goals like Coq does. 
There are simple tactics such as `rewrite` (abbrev. `rw`) which rewrites the goal according to definitions, 
as well as powerful tactics such as `simp` (simplify) and `refl` (reflection) which apply a collection of 
common-sense theorems to simplify or even prove the goal in one go.

The operator `<+:` means `is_prefix` and `<:+` means `is_suffix`. 
They are both defined in `data.list` in mathlib.

The proof of the length is as such:

```lean
begin
  rw leftpad, simp,
  rw [add_comm, nat.sub_add_eq_max]
end
```

`simp` doesn't carry us all the way this time because `add_comm` is not `@[simp]`.
It cannot because it would loop on itself.
We need the `nat` version of `sub_add_eq_max` because the default one is proved for group, 
but `length` is defined as `nat` which is not a group due to lack of inverse.
Therefore, it has to be proven for `nat` separately in `data.nat.basic`.

That's it!
