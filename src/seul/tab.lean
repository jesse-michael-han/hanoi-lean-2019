/- Propositional tableaux prover from Jeremy Avigad's lecture notes. -/

open expr tactic classical

variables {p q r s : Prop}
variables {a b c d e : Prop}

section

local attribute [instance] classical.prop_decidable

  theorem not_or_of_imp (h : a → b) : ¬ a ∨ b :=
  if ha : a then or.inr (h ha) else or.inl ha

  theorem imp_iff_not_or : (a → b) ↔ (¬ a ∨ b) :=
  ⟨not_or_of_imp, or.neg_resolve_left⟩

  theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  iff_iff_implies_and_implies _ _

  theorem not_not : ¬¬a ↔ a :=
  iff.intro by_contradiction not_not_intro

  theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
  ⟨λ h, ⟨λ ha, h (or.inl ha), λ hb, h (or.inr hb)⟩,
   λ ⟨h₁, h₂⟩ h, or.elim h h₁ h₂⟩

  theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b)
  | ⟨ha, hb⟩ := or.elim h (absurd ha) (absurd hb)

  theorem not_and_distrib : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨λ h, if ha : a then or.inr (λ hb, h ⟨ha, hb⟩) else or.inl ha, not_and_of_not_or_not⟩

end

meta def normalize : tactic unit :=
`[ try { simp only
   [ not_or_distrib,
     not_and_distrib,
     not_not,
     imp_iff_not_or,
     not_true_iff,
     not_false_iff,
     iff_def ] at * } ]

meta def find_conj : list expr → tactic expr
| []        := failed
| (e :: es) := do t ← infer_type e,
                  match t with
                  | `(%%a ∧ %%b) := return e
                  | _            := find_conj es
                  end

meta def find_disj : list expr → tactic expr
| []        := failed
| (e :: es) := do t ← infer_type e,
                  match t with
                  | `(%%a ∨ %%b) := return e
                  | _            := find_disj es
                  end

meta def split_conj : tactic unit :=
do l ← local_context,
   e ← find_conj l,
   cases e,
   skip

meta def split_conjs : tactic unit :=
repeat split_conj

meta def split_disj : tactic unit :=
do l ← local_context,
   e ← find_disj l,
   cases e,
   skip

meta def proof_by_contradiction : tactic unit :=
do refine ``(classical.by_contradiction _),
   intro `_,
   skip

meta def tab_aux : tactic unit :=
do split_conjs,
   contradiction <|>
     (split_disj >> tab_aux >> tab_aux)

meta def tab : tactic unit :=
do proof_by_contradiction,
   normalize,
   tab_aux

example : a ∧ b → b ∧ a := by tab
example : a ∧ (a → b) → b := by tab

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by tab
example : p ∨ q ↔ q ∨ p := by tab

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by tab
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by tab

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by tab
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by tab

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by tab
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by tab
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by tab
example : ¬p ∨ ¬q → ¬(p ∧ q) := by tab
example : ¬(p ∧ ¬p) := by tab
example : p ∧ ¬q → ¬(p → q) := by tab
example : ¬p → (p → q) := by tab
example : (¬p ∨ q) → (p → q) := by tab
example : p ∨ false ↔ p := by tab
example : p ∧ false ↔ false := by tab
example : ¬(p ↔ ¬p) := by tab
example : (p → q) → (¬q → ¬p) := by tab

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by tab
example : ¬(p ∧ q) → ¬p ∨ ¬q := by tab
example : ¬(p → q) → p ∧ ¬q := by tab
example : (p → q) → (¬p ∨ q) := by tab
example : (¬q → ¬p) → (p → q) := by tab
example : p ∨ ¬p := by tab
example : (((p → q) → p) → p) := by tab

example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∨ c := by tab

example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∧ ¬ c := by tab

example : ((a → b) → a) → a := by tab

example : (a → b) ∧ (b → c) → a → c := by tab

example (α : Type) (x y z w : α) :
  x = y ∧ (x = y → z = w) → z = w := by tab

example : ¬ (a ↔ ¬ a) := by tab
