import algebra.pi_instances
set_option old_structure_cmd true

universe variables u

/-
  A non-unital ring or rng is a ring without unit. According to ncatlab
  https://ncatlab.org/nlab/show/nonunital+ring

  Definition 2.1. A nonunital ring or rng is a set R with operations of addition and multiplication, such that:

  * R is a semigroup under multiplication;
  * R is an abelian group under addition;
  * multiplication distributes over addition.
-/

/- Define rng in Lean. Use a definition similar to `ring`. Replace the following definition with the correct definition. -/
class rng (α : Type u) extends ring α

/- Formulate and show that every ring is a rng. -/

variables {α : Type u} [rng α] {a b c x y z w : α} {n m : ℤ}

/- Prove the following lemma. -/
lemma distrib2 : (x + y) * (z + w) = x * z + x * w + y * z + y * w :=
sorry

/- Construct the following instance.
For each field, first write a lemma that proves that field.
There are very similar lemmas proven for rings, try to copy those and modify where needed -/

instance rng.mul_zero_class : mul_zero_class α :=
sorry

/- Formulate and prove lemmas that state -(a * b) = a * -b = -a * b (see mathlib for similar lemmas) -/

/- Prove that a * (b - c) = a * b - a * c (see mathlib for similar lemmas) -/

/- Prove the following lemmas by induction on n.
  Try to prove one with the `induction` tactic, and one with the equation compiler. -/
lemma rng.nat_smul_mul_left : n • a * b = n • (a * b) := sorry

lemma rng.nat_smul_mul_right : a * n • b = n • (a * b) := sorry

/-
  The following lemmas are tricky, so they are provided for you.
  You can uncomment them in VSCode by selecting them and pressing `ctrl+/`
  The proof assumes that `rng.neg_mul_eq_neg_mul` is the name of the lemma that `-(a * b) = -a * b`.
  Make sure you understand the proofs.
-/
-- lemma rng.smul_mul_left : ∀{n : ℤ}, n • a * b = n • (a * b)
-- | (n : ℕ) := rng.nat_smul_mul_left
-- | -[1+n]  := show (-↑(n+1) : ℤ) • a * b  = (-↑(n+1) : ℤ) • (a * b),
--   by { rw [neg_smul, neg_smul, ←rng.neg_mul_eq_neg_mul], congr' 1,
--        apply rng.nat_smul_mul_left }

-- lemma rng.smul_mul_right : ∀{n : ℤ}, a * n • b = n • (a * b)
-- | (n : ℕ) := rng.nat_smul_mul_right
-- | -[1+n]  := show a * (-↑(n+1) : ℤ) • b  = (-↑(n+1) : ℤ) • (a * b),
--   by { rw [neg_smul, neg_smul, ←rng.neg_mul_eq_mul_neg], congr' 1,
--        apply rng.nat_smul_mul_right }


/- Prove that n • (m • a) = m • (n • a) -/

/- We will now construct the unitisation of a non-unital ring. See ncatlab:

Definition 3.1. Given a non-unital ring A, then its unitisation is the ring F(A) obtained by freely adjoining an identity element, hence the ring whose underlying abelian group is the direct sum Z⊕A of A with the integers, and whose product operation is defined by

(n₁,a₁)(n₂,a₂) = (n₁n₂, n₁a₂ + n₂a₁ + a₁a₂),
where for n∈Z and a∈A we set na = a + a + ⋯ + a with n summands.
-/
def unitisation (α : Type u) : Type u := ℤ × α

namespace unitisation

/- Define multiplication so that (n₁,a₁)(n₂,a₂) = (n₁n₂, n₁a₂ + n₂a₁ + a₁a₂).
  Use `•` to multiply a integer with a element of α. -/
instance : has_mul (unitisation α) :=
sorry

/- Fill in the blanks, Prove the following rewrite rules. Also add them as simplification lemmas. -/
lemma mk_mul_mk : (⟨n, a⟩ * ⟨m, b⟩ : unitisation α) = sorry :=
sorry

lemma mul_fst {x y : unitisation α} : (x * y).fst = sorry :=
sorry

lemma mul_snd {x y : unitisation α} :
  (x * y).snd = sorry :=
sorry

/- Now prove that this is a ring. Lean already knows it is a commutative group under addition using instance `prod.add_comm_group`. -/
instance : ring (unitisation α) := sorry


end unitisation
