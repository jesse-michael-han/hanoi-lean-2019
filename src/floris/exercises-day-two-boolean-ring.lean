import order.boolean_algebra

open lattice

/-
EXERCISE:

In mathematics, a Boolean ring R is a ring for which x² = x for all x in R.

Define a class of boolean rings. It should extend the typeclass of rings.

-/

class boolean_ring (α : Type*) := sorry

open boolean_ring


universe u

variables {α : Type u} [boolean_ring α]


/-
Since the join operation ∨ in a Boolean algebra is often written additively, it makes sense in this context to denote ring addition by ⊕, a symbol that is often used to denote exclusive or.

Given a Boolean ring R, for x and y in R we can define

    x ∧ y = xy,

    x ∨ y = x ⊕ y ⊕ xy,

    ¬x = 1 ⊕ x.

These operations then satisfy all of the axioms for meets, joins, and complements in a Boolean algebra. Thus every Boolean ring becomes a Boolean algebra.
-/
local notation x ` ⊕ ` y := (x : α) + (y : α)

/- Every Boolean ring R satisfies x ⊕ x = 0 for all x in R, because we know

    x ⊕ x = (x ⊕ x)² = x² ⊕ x² ⊕ x² ⊕ x² = x ⊕ x ⊕ x ⊕ x

and since (R,⊕) is an abelian group, we can subtract x ⊕ x from both sides of this equation, which gives x ⊕ x = 0. A similar proof shows that every Boolean ring is commutative:

    x ⊕ y = (x ⊕ y)² = x² ⊕ xy ⊕ yx ⊕ y² = x ⊕ xy ⊕ yx ⊕ y

 and this yields xy ⊕ yx = 0, which means xy = yx (using the first property above). -/

/- EXERCISE: Prove a lemma which says that ∀ x : α, x ⊕ x = 0 and a lemma that multiplication commutes.-/


/- EXERCISE: Given the boolean_ring instance on α, construct the boolean_algebra instance on α. -/

/- the inf operation should be x * y, the sup operation should be x ⊕ y ⊕ x * y, and the complement operation should be 1 ⊕ x. -/

instance boolean_algebra_of_boolean_ring {α : Type*} [boolean_ring α] : boolean_algebra α :=
{!_!} -- use the hole command for creating a structure stub
