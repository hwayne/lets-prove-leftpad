/- More concise version of the leftpad specification and proofs
   for strings only
 -/

def leftPad (n: Nat) (a: Char) (s: String) : String :=
  "".pushn a (n - s.length) ++ s

theorem leftpad_length (n: Nat) (a: Char) (s: String)
    : (leftPad n a s).length = max n (s.length) :=
  by simp [leftPad, Nat.sub_add_eq_max]

theorem String.data_pushn (s: String) (c: Char) (n: Nat)
    : (s.pushn c n).data = s.data ++ (List.replicate n c) := by
  unfold String.pushn
  refine n.recOn ?z ?s
  case z => simp [Nat.repeat]
  case s =>
    intro n (ih: (Nat.repeat (·.push c) n s).data = s.data ++ List.replicate n c)
    simp [Nat.repeat, ih]
    exact Eq.symm List.replicate_succ'

theorem leftpad_prefix (n: Nat) (a: Char) (s: String)
    : (List.replicate (n - s.length) a) <+: (leftPad n a s).data := by
  unfold leftPad
  simp [String.data_append, String.data_pushn]

theorem leftpad_suffix (n: Nat) (a: Char) (s: String)
    : s.data <:+ (leftPad n a s).data := by
  unfold leftPad
  simp [String.data_append, String.data_pushn]
