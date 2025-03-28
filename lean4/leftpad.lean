/- More simplistic and straightforward version of the
   leftpad specification and proofs in two versions:
   for arbitrary lists in general and for strings specifically
 -/

variable {α : Type}

def leftpad (n : Nat) (a : α) (l : List α) : List α :=
  List.replicate (n - l.length) a ++ l

#eval List.toString (leftpad 5 'b' (String.toList "ac"))

theorem leftpad_length (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n (l.length) := by
  simp [leftpad, Nat.sub_add_eq_max]


theorem leftpad_prefix [BEq α] [LawfulBEq α] (n : Nat) (a : α) (l : List α) :
    (List.replicate (n - l.length) a).isPrefixOf (leftpad n a l) := by
  simp [leftpad]


theorem leftpad_suffix [BEq α] [LawfulBEq α] (n : Nat) (a : α) (l : List α) :
    l.isSuffixOf (leftpad n a l) := by
  simp [leftpad]


namespace Strings

def leftpad (n : Nat) (a : Char) (s : String) : String :=
  "".pushn a (n - s.length) ++ s

#eval leftpad 5 'b' "ac"

theorem leftpad_length (n: Nat) (a: Char) (s: String)
    : (leftpad n a s).length = max n (s.length) :=
  by simp [leftpad, Nat.sub_add_eq_max]

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
    : (List.replicate (n - s.length) a) <+: (leftpad n a s).data := by
  unfold leftpad
  simp [String.data_append, String.data_pushn]

theorem leftpad_suffix (n: Nat) (a: Char) (s: String)
    : s.data <:+ (leftpad n a s).data := by
  unfold leftpad
  simp [String.data_append, String.data_pushn]
