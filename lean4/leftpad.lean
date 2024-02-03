

variable {α : Type}

def leftpad (n : Nat) (a : α) (l : List α) : List α :=
  List.replicate (n - l.length) a ++ l

#eval List.toString (leftpad 5 'b' (String.toList "ac"))

theorem leftpad_length (n : Nat) (a : α) (l : List α) : (leftpad n a l).length = max n (l.length) := by
  simp [leftpad, Nat.max_def]
  unfold ite
  cases (Nat.decLe n (List.length l)) with
  | isTrue h =>
    dsimp
    rw [Nat.sub_eq_zero_of_le]
    simp
    assumption
  | isFalse h =>
    dsimp
    rw [Nat.sub_add_cancel]
    apply Nat.le_of_lt (Nat.gt_of_not_le h)


theorem prefix_concat [BEq α] [LawfulBEq α] (l m : List α) : l.isPrefixOf (l ++ m) := by
  unfold List.isPrefixOf
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp
    unfold List.isPrefixOf
    rw [ih]

theorem leftpad_prefix [BEq α] [LawfulBEq α] (n : Nat) (a : α) (l : List α) :
(List.replicate (n - l.length) a).isPrefixOf (leftpad n a l) := by
  simp [leftpad]
  apply prefix_concat (List.replicate (n - List.length l) a) l


theorem suffix_concat [BEq α] [LawfulBEq α] (l m : List α) : m.isSuffixOf (l ++ m) := by
  unfold List.isSuffixOf
  rw [List.reverse_append]
  apply prefix_concat (List.reverse m) (List.reverse l)

theorem leftpad_suffix [BEq α] [LawfulBEq α] (n : Nat) (a : α) (l : List α) :
l.isSuffixOf (leftpad n a l) := by
  simp [leftpad]
  apply suffix_concat


namespace Strings

def leftpad (n : Nat) (a : Char) (s : String) : String :=
  "".pushn a (n - s.length) ++ s

#eval leftpad 5 'b' "ac"


theorem length_append_distrib (s t : String) : (s ++ t).length = s.length + t.length := by
  simp [HAppend.hAppend, Append.append, String.append, String.length]

theorem length_push_data_succ (s : String) (a : Char) : (s.push a).data.length = s.data.length + 1 := by
  simp [String.push, String.length]

theorem length_pushn_zero (s : String) (a : Char) : (s.pushn a 0).length = s.length := by
  simp [String.pushn, Nat.repeat]

theorem length_pushn_sub (n : Nat) (s : String) (a : Char) (h : n > 0) : (s.pushn a n).length = s.length + n := by
  simp [String.length, String.pushn]
  induction n with
  | zero =>
    contradiction
  | succ m ih =>
    unfold Nat.repeat
    rw [length_push_data_succ]
    induction m with
    | zero =>
      simp [Nat.repeat]
    | succ k =>
      rw [ih]
      simp_arith
      simp_arith

theorem leftpad_length (n : Nat) (a : Char) (s : String) : (leftpad n a s).length = max n (s.length) := by
  simp [leftpad, Nat.max_def]
  unfold ite
  cases (Nat.decLe n (String.length s)) with
  | isTrue h =>
    dsimp
    rw [length_append_distrib ("".pushn a (n - s.length)) s]
    have z : n - s.length = 0 := Nat.sub_eq_zero_of_le h
    rw [z, length_pushn_zero]
    simp [String.length]
  | isFalse h =>
    dsimp
    rw [length_append_distrib ("".pushn a (n - s.length)) s]
    have ngt : n - s.length > 0 := by
      simp [Nat.gt_of_not_le h, Nat.sub_ne_zero_of_lt, Nat.zero_lt_sub_of_lt]
    rw [length_pushn_sub]
    . simp [String.length]
      apply Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le h))
    . assumption


theorem string_data_concat (s t : String) : (s ++ t).data = s.data ++ t.data := by
  simp [HAppend.hAppend, Append.append, String.append]

theorem replicate_cons (n : Nat) (a : α) : List.replicate n a ++ [a] = a :: List.replicate n a := by
  induction n with
  | zero => simp [List.replicate]
  | succ m ih =>
    simp [List.replicate, ih]

theorem repeat_empty (c : Char) (n : Nat) : (n.repeat (fun s => s.push c) "").data = List.replicate n c := by
  induction n with
  | zero =>
    simp [Nat.repeat]
  | succ m ih =>
    simp [Nat.repeat, String.push]
    simp [String.push] at ih
    rw [ih]
    simp [replicate_cons]

theorem pushn_succ (m : Nat) (a : Char) : ("".pushn a m.succ).data = a :: ("".pushn a m).data := by
  simp [String.pushn, repeat_empty]

theorem pushn_empty_replicate (n : Nat) (a : Char) : ("".pushn a n).data = List.replicate n a := by
  induction n with
  | zero =>
    simp [String.pushn, Nat.repeat]
  | succ m ih =>
    simp [Nat.repeat]
    rw [<-ih, pushn_succ]

theorem leftpad_prefix (n : Nat) (a : Char) (s : String) :
(List.replicate (n - s.length) a).isPrefixOf (leftpad n a s).data := by
  simp [leftpad, string_data_concat]
  rw [pushn_empty_replicate]
  simp [prefix_concat]


theorem leftpad_suffix (n : Nat) (a : Char) (s : String) :
s.data.isSuffixOf (leftpad n a s).data := by
  simp [leftpad, string_data_concat]
  apply suffix_concat
