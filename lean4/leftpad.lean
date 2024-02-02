

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
  apply suffix_concat (List.replicate (n - List.length l) a) l
