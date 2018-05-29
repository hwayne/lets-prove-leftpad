
import data.list.basic

section unique

variables {α : Type*} [decidable_eq α]

def unique : list α → list α
 | [] := []
 | (x :: xs) :=
   if x ∈ xs
     then unique xs
     else x :: unique xs

lemma mem_unique (x : α) (xs : list α) :
  x ∈ unique xs ↔ x ∈ xs :=
begin
  induction xs with x' xs ; simp!,
  by_cases x' ∈ xs ; simp *,
  split ; intro h,
  { simp * },
  { cases h ; cc, },
end

lemma nodup_unique (xs : list α) :
  (unique xs).nodup :=
begin
  induction xs with x xs ; simp!,
  by_cases x ∈ xs ; simp [*,mem_unique],
end

end unique
