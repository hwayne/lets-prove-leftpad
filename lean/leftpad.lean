
import data.list.basic

section left_pad

variables {α : Type*}

open nat

lemma list.cons_repeat (c : α) :
  Π  (n : ℕ), c :: list.repeat c n = list.repeat c n ++ [c] :=
by { intro, symmetry, induction n ; simp *, }

lemma list.take_append (xs ys : list α) (n : ℕ)
  (h : xs.length = n) :
  (xs ++ ys).take n = xs :=
by { subst n, induction xs ; simp! [add_one,*], }

lemma list.drop_append (xs ys : list α) (n : ℕ)
  (h : xs.length = n) :
  (xs ++ ys).drop n = ys :=
by { subst n, induction xs ; simp! [add_one,*], }

def left_pad_aux (c : α) : ℕ → list α → list α
 | 0 xs := xs
 | (succ n) xs := left_pad_aux n (c :: xs)

def left_pad (c : α) (n : ℕ) (x : list α) : list α :=
left_pad_aux c (n - x.length) x

variables (c : α) (n : ℕ) (x : list α)

lemma left_pad_def
: left_pad c n x = list.repeat c (n - x.length) ++ x :=
begin
  simp [left_pad],
  generalize : (n - list.length x) = k,
  induction k generalizing x
  ; simp! [add_one,add_succ,succ_add,list.cons_repeat,*],
end

lemma length_left_pad
: (left_pad c n x).length = max n x.length :=
begin
  simp [left_pad_def],
  cases le_total n x.length with Hk Hk,
  { rw max_eq_right Hk,
    rw ← nat.sub_eq_zero_iff_le at Hk,
    simp *, },
  { simp [max_eq_left Hk],
    rw [← nat.add_sub_assoc Hk,nat.add_sub_cancel_left] },
end

lemma left_pad_prefix
: ∀ c' ∈ (left_pad c n x).take (n - x.length), c' = c :=
by { rw [left_pad_def,list.take_append] ,
     { intro, apply list.eq_of_mem_repeat },
     simp! , }

lemma left_pad_suffix
: (left_pad c n x).drop (n - x.length) = x :=
by simp [left_pad_def,list.drop_append]

end left_pad
