import order.lattice data.nat.gcd tactic tactic.explode

class lattice' (α : Type*) extends lattice.has_inf α, lattice.has_sup α :=
(inf_comm : ∀ x y : α, x ⊓ y = y ⊓ x)
(inf_assoc : ∀ x y z : α, x ⊓ y ⊓ z = x ⊓ (y ⊓ z))
(sup_comm : ∀ x y : α, x ⊔ y = y ⊔ x)
(sup_assoc : ∀ x y z : α, x ⊔ y ⊔ z = x ⊔ (y ⊔ z))
(inf_absorb : ∀ x y : α, x ⊓ (x ⊔ y) = x)
(sup_absorb : ∀ x y : α, x ⊔ (x ⊓ y) = x)

namespace lattice'

attribute [ematch] inf_comm inf_assoc sup_comm sup_assoc inf_absorb sup_absorb

-- inside the namespace, you can refer to the axioms without a prefix

variables {α : Type*} [lattice' α]

lemma try_me (x : α) : x ⊔ x = x :=
begin
  conv {to_lhs, congr, skip, rw[<-inf_absorb x x]},
  rw[sup_absorb x _]
end

@[ematch]theorem sup_idem (x : α) : x ⊔ x = x := by finish

@[ematch]theorem inf_idem (x : α) : x ⊓ x = x := by finish

protected def le (x y : α) := x = x ⊓ y

instance : has_le α := ⟨lattice'.le⟩

@[ematch]lemma le_unfold {x y : α} : x ≤ y ↔ x = x ⊓ y := by refl

@[ematch]theorem le_def (x y : α) : (x ≤ y) = (x = x ⊓ y) := rfl

@[ematch]theorem le_refl (x : α) : x ≤ x := by rw [le_def, inf_idem]

-- you can use `rw le_def at *` to unfold the definition everywhere

-- Wikipedia also tells you how to prove this one:

@[ematch]theorem le_def' (x y : α) : (x ≤ y) ↔ (y = x ⊔ y) :=
by split; intros; finish

@[ematch]theorem le_trans {x y z : α} (h : x ≤ y) (h' : y ≤ z) : x ≤ z := by finish

@[ematch]theorem le_antisymm {x y : α} (h : x ≤ y) (h' : y ≤ x) : x = y := by finish

@[ematch]theorem le_sup_left (x y : α) : x ≤ x ⊔ y := by finish

@[ematch]theorem le_sup_right (x y : α) : y ≤ x ⊔ y := by finish

@[ematch]theorem sup_le {x y z : α} (h₁ : x ≤ z) (h₂ : y ≤ z) : x ⊔ y ≤ z := by finish

@[ematch]theorem inf_le_left (x y : α) : x ⊓ y ≤ x := by finish

@[ematch]theorem inf_le_right (x y : α) : x ⊓ y ≤ y := by finish

@[ematch]theorem le_inf {x y z : α} (h₁ : x ≤ y) (h₂ : x ≤ z) : x ≤ y ⊓ z := by finish

end lattice'

-- instance to_lattice : lattice.lattice α :=
-- { sup           := λ x y, x ⊔ y,
--   inf           := λ x y, x ⊓ y,
--    le           := lattice'.le,
--    le_refl      := le_refl,
--    le_trans     := @le_trans _ _,
--    le_antisymm  := @le_antisymm _ _,
--    le_sup_left  := le_sup_left,
--    le_sup_right := le_sup_right,
--    sup_le       := @sup_le _ _,
--    inf_le_left  := inf_le_left,
--    inf_le_right := inf_le_right,
--    le_inf       := @le_inf _ _ }

-- end lattice'

/- This part is required of graduate students only. It shows that, conversely, 
   a lattice is a lattice'. 
   
   To do this, you will want to take a look at the theorems in order.lattice. 
-/

namespace lattice

variables {α : Type*} [lattice α]

theorem inf_absorb (x y : α) : x ⊓ (x ⊔ y) = x :=
by {apply le_antisymm; finish}

theorem sup_absorb (x y : α) : x ⊔ (x ⊓ y) = x :=
by {apply le_antisymm; finish}

-- For this, you will want to you use the badly named theorem, `inf_of_le_left`.
-- (It should be named `inf_eq_of_le_left`.)

theorem le_iff (x y : α) : x ≤ y ↔ x = x ⊓ y :=
by {split; intros, {apply le_antisymm; finish}, finish}

end lattice

/-
Optional: show that the natural numbers form a lattice where the ordering
is the divsibility relation, sup is the least common multiple, and inf is
the greatest common divisor.

To do this, look at the theorems in data.nat.gcd.

Remember, to type `x ∣ y`, use `\|`.
-/

section
open lattice nat

instance nat_div_lattice : lattice nat :=
{ le           := λ x y, x ∣ y,
  sup          := lcm,
  inf          := gcd,
  le_refl      := sorry,
  le_trans     := sorry,
  le_antisymm  := sorry,
  le_sup_left  := sorry,
  le_sup_right := sorry,
  sup_le       := sorry,
  inf_le_left  := sorry,
  inf_le_right := sorry,
  le_inf       := sorry }

end
