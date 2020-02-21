import data.nat.basic
import data.list
open string list nat

universes u
variables {α : Type u}

@[simp] def leftpad (n : ℕ) (a : α) (l : list α) : list α :=
repeat a (n - length l) ++ l

#eval as_string (leftpad 5 'b' (to_list "ac"))

theorem leftpad_length (n : ℕ) (a : α) (l : list α) : 
length (leftpad n a l) = max n (length l) :=
begin
  simp,
  rw [add_comm, sub_add_eq_max]
end

theorem leftpad_prefix [decidable_eq α] (n : ℕ) (a : α) (l : list α) :
(repeat a (n - length l)) <+: (leftpad n a l) := by simp

theorem leftpad_suffix [decidable_eq α] (n : ℕ) (a : α) (l : list α) :
l <:+ (leftpad n a l) := by simp
