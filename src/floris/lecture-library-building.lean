/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn.

A lecture on library-building.
-/
import algebra.group order.boolean_algebra tactic.library_search
data.vector

set_option old_structure_cmd true
universe variable u

/-
  Best practices:
-/

/-
  Use good names: https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/naming.md
-/

#print nat.succ_ne_zero
#print mul_zero -- the name could be mul_zero_eq, but we shorten it
#print mul_one
#print le_iff_lt_or_eq
#print neg_neg
#print add_lt_add_of_lt_of_le
#print mul_assoc

example {p q : Prop} (h : p ∧ q) :
  p :=
h.left -- and.left h

open nat
example (n : ℕ) : succ n > 0 :=
by library_search
-- library_search is useful to find a lemma in the library. You need to know the exact conclusion of the lemma (and import tactic.library_search).

/-
  Use good style: https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/style.md
-/

/-
  Good proving practice
    * Try to work in great generality (c.f. Fréchet derivative)
    * Use bi-implications whenever possible
    * Write equations and bi-implications so that the RHS is simpler than the LHS (if possible)
-/

/-
  IMPORTANT: Copy-paste from a similar development:
    - The existing library probably used the right explicit/implicit arguments
    - The existing library probably used the right style
    - The existing library probably made good design decisions
-/

/-
  Look through mathlib to see what parts already exists
-/

/-
  After you complete a lemma, clean up the proof afterwards:
    * replace `intro x, intro y` by `intros x y`
    * remove `simp` (or other automation) if it didn't close  goal
    * If the proof fits on one line, replace `begin ... end` with `by { ... }`
    * etc.
-/

/-
  As a demo, let's build a little library of quasigroups:
  https://en.wikipedia.org/wiki/Quasigroup
-/

/-
  From Wikipedia:
  A quasigroup (Q, ∗, \, /) is a type (2,2,2) algebra (i.e., equipped with three binary operations) satisfying the identities:
  y = x ∗ (x \ y),
  y = x \ (x ∗ y),
  y = (y / x) ∗ x,
  y = (y ∗ x) / x.
-/

#print semigroup -- we use a definition similar to semigroup
-- \ is left division, abbreviated as ldiv
-- / right division, abbreviated as rdiv
class quasigroup (α : Type u) extends has_mul α, has_div α, has_sdiff α :=
(mul_ldiv : ∀ x y : α, x * (x \ y) = y)
(ldiv_mul : ∀ x y : α, x \ (x * y) = y)
(rdiv_mul : ∀ x y : α, (x / y) * y = x)
(mul_rdiv : ∀ x y : α, (x * y) / y = x)

-- x \ y is the unique element z such that x * z = y

variables {α : Type u} [quasigroup α]

lemma mul_ldiv (x y : α) : x * (x \ y) = y :=
quasigroup.mul_ldiv x y
lemma ldiv_mul (x y : α) : x \ (x * y) = y :=
quasigroup.ldiv_mul x y
lemma mul_rdiv (x y : α) : (x * y) / y = x :=
quasigroup.mul_rdiv x y
lemma rdiv_mul (x y : α) : (x / y) * y = x :=
quasigroup.rdiv_mul x y

@[simp] lemma ldiv_eq_iff_mul_eq {x y z : α} :
  x \ y = z ↔ x * z = y :=
begin
  split,
  { intro h, rw [← h, mul_ldiv] },
  { intro h, rw [← h, ldiv_mul] }
end

@[simp] lemma rdiv_eq_iff_mul_eq {x y z : α} :
  x / y = z ↔ z * y = x :=
begin
  split,
  { intro h, rw [← h, rdiv_mul] },
  { intro h, rw [← h, mul_rdiv] }
end

/-
  Given an abelian group, (A, +), taking its subtraction operation as quasigroup multiplication yields a quasigroup (A, −)
-/

@[simp] lemma add_add_neg_cancel {α} [add_comm_group α] (x y : α) : x + (y + -x) = y :=
by { rw [add_comm], simp }

def sub_quasigroup (α : Type u) := α
instance {α} [add_comm_group α] : quasigroup (sub_quasigroup α) :=
{ mul := λ x y, (x - y : α),
  div := λ x y, (x + y : α),
  sdiff := λ x y, (x - y : α),
  ldiv_mul := by { intros, simp },
  mul_ldiv := by { intros, simp },
  mul_rdiv := by { intros, simp },
  rdiv_mul := by { intros, simp } }

/-
  A loop is a quasigroup with an identity element; that is, an element, e, such that
  x ∗ e = x and e ∗ x = x for all x in Q.
  It follows that the identity element, e, is unique, and that every element of Q has unique left and right inverses (which need not be the same).
-/
#print monoid -- we use a definition similar to monoid.

class loop (α : Type u) extends quasigroup α, has_one α :=
(one_mul : ∀ a : α, 1 * a = a) (mul_one : ∀ a : α, a * 1 = a)



/-
  Every group is a loop.
-/
#print group
instance group.to_loop {α : Type u}
  [h : group α] : loop α :=
{ mul := (*),
  div := λ x y, x * y⁻¹,
  sdiff := λ x y, x⁻¹ * y,
  mul_ldiv := by { intros, simp },
  ldiv_mul := by { intros, simp },
  rdiv_mul := by { intros, simp },
  mul_rdiv := by { intros, simp },
  ..h }



/-
  A loop that is associative is a group
-/

def loop.to_group {α} [h : loop α] (h_assoc : ∀ x y z : α, (x * y) * z = x * (y * z)) : group α :=
{ mul := (*),
  mul_assoc := h_assoc,
  inv := λ x, 1 / x,
  mul_left_inv := λ x, by apply rdiv_mul,
  ..h }

------------- Q&A -------------

/- It is better not to put `quasigroup α` as an argument.
  If we did that, we would have to specify two arguments to state that α has a loop structure -/
class loop' (α : Type u) [quasigroup α] extends has_one α :=
(one_mul : ∀ a : α, 1 * a = a) (mul_one : ∀ a : α, a * 1 = a)

def loop'.to_group {α} [quasigroup α] [h : loop' α] (h_assoc : ∀ x y z : α, (x * y) * z = x * (y * z)) : group α :=
sorry

instance group.to_quasigroup {α : Type u}
  [h : group α] : quasigroup α :=
  sorry

/- The following instance doesn't type-check if we remove the previous instance. -/
instance group.to_loop' {α : Type u}
  [h : group α] : loop' α :=
sorry

/- If you want to use the notation * for an operation of type
  α → α → α (for some α), you can should make an instance of has_mul. Example: -/

instance list.has_mul {α : Type u} : has_mul (list α) :=
{ mul := list.append }

/- If you want to make it a local notation (for only this file), use: -/
def list.has_mul' {α : Type u} : has_mul (list α) :=
{ mul := list.append }
local attribute [instance] list.has_mul'

/- if you have an operation with a different type, define (local) notation for it, and use a symbol other than *
  -/
constant inner_product {n : ℕ} : vector ℕ n → vector ℕ n → ℕ
local infix ⬝ := inner_product