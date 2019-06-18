open expr tactic classical

variables {p q r s : Prop}
variables {a b c d e : Prop}

section 

local attribute [instance] classical.prop_decidable
  
  theorem not_or_of_imp (h : a → b) : ¬ a ∨ b := sorry
  
  theorem imp_iff_not_or : (a → b) ↔ (¬ a ∨ b) := sorry
  
  theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) := sorry
  
  theorem not_not : ¬¬a ↔ a := sorry
  
  theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b := sorry
  
  theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) := sorry
  
  theorem not_and_distrib : ¬ (a ∧ b) ↔ ¬a ∨ ¬b := sorry

end 

meta def normalize : tactic unit :=
`[ try { simp only
   [ not_or_distrib,
     not_and_distrib,
     not_not,
     imp_iff_not_or,
     not_true_iff,
     not_false_iff,
     iff_def ] at *} ]

/- Given a list of expr of hypotheses, find an expr of a 
   conjunctive hypothesis in the list and return it. -/
meta def find_conj : list expr → tactic expr := sorry

/- Given a list of expr of hypotheses, find an expr of a 
   disjunctive hypothesis in the list and return it. -/
meta def find_disj : list expr → tactic expr := sorry

/- Find and split a conjunction. -/
meta def split_conj : tactic unit := sorry

/- Split all conjunctions using split_conj. -/
meta def split_conjs : tactic unit := sorry

/- Find and split a disjunction. -/
meta def split_disj : tactic unit := sorry

/- Given a goal of the form Γ ⊢ φ, reduce it to the goal Γ, ¬φ ⊢ ⊥ -/
meta def go_by_contradiction : tactic unit := sorry

/- The main proof search loop. First, split all conjunctions.
   If the result has complementary literals, discharge the goal. 
   If not, find a disjunction, split it, and discharge the new
   subgoals by entering the proof search loop again. -/
meta def tab_aux : tactic unit := sorry

/- Normalize goal and enter proof search loop. -/
meta def tab : tactic unit := sorry 

#exit

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

example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∨ c :=
by tab

example (h₁ : a ∧ b) (h₂ : b ∧ ¬ c) : a ∧ ¬ c :=
by tab

example : ((a → b) → a) → a :=
by tab

example : (a → b) ∧ (b → c) → a → c :=
by tab

example (α : Type) (x y z w : α) :
  x = y ∧ (x = y → z = w) → z = w :=
by tab

example : ¬ (a ↔ ¬ a) :=
by tab