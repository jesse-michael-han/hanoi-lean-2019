open classical

/- Fill in the `sorry`s below -/

local attribute [instance, priority 0] prop_decidable

example (p : Prop) : p ∨ ¬ p :=
begin
  by_cases p,
  { sorry },
  { sorry }
end

example (p : Prop) : p ∨ ¬ p :=
begin
  by_cases h' : p,
  { sorry },
  { sorry }
end

/-
Give a calculational proof of the theorem log_mul below. You can use the 
rewrite tactic `rw` (and `calc` if you want), but not `simp`.

These objects are actually defined in mathlib, but for now, we'll
just declare them.
-/

constant real : Type
@[instance] constant  orreal : ordered_ring real
constants (log exp : real → real)
constant  log_exp_eq : ∀ x, log (exp x) = x
constant  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
constant  exp_pos    : ∀ x, exp x > 0
constant  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
sorry

example (y : real) (h : y > 0)  : exp (log y) = y :=
sorry

theorem log_mul' {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
sorry

section

variables {p q r : Prop}

example : (p → q) → (¬q → ¬p) :=
sorry

example : (p → (q → r)) → (p ∧ q → r) :=
sorry

example : p ∧ ¬q → ¬(p → q) :=
sorry

example : (¬p ∨ q) → (p → q) :=
sorry

example : (p ∨ q → r) → (p → r) ∧ (q → r) :=
sorry

example : (p → q) → (¬p ∨ q) :=
sorry

end

section

variables {α β : Type} (p q : α → Prop) (r : α → β → Prop)

example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x :=
sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
sorry

example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y :=
sorry

theorem e1 : (¬ ∃ x, p x) → ∀ x, ¬ p x :=
sorry

example : (¬ ∀ x, ¬ p x) → ∃ x, p x :=
sorry

example : (¬ ∀ x, ¬ p x) → ∃ x, p x :=
sorry

end

section

/-
There is a man in the town who is the barber. The barber shaves all men who do not shave themselves.

Does the barber shave himself?
-/

variables (man : Type) (barber : man)
variable  (shaves : man → man → Prop)

example (H : ∀ x : man, shaves barber x ↔ ¬ shaves x x) : false :=
sorry

end

section

variables {α : Type} (p : α → Prop) (r : Prop) (a : α)

include a
example : (r → ∃ x, p x) → ∃ x, (r → p x) :=
sorry

end

/-
Prove the theorem below, using only the ring properties of ℤ enumerated 
in Section 4.2 and the theorem sub_self. You should probably work out 
a pen-and-paper proof first.
-/

example (x : ℤ) : x * 0 = 0 :=
sorry

section
open list

variable {α : Type*}
variables s t : list α 
variable a : α

example : length (s ++ t) = length s + length t :=
sorry

end

/-
Define an inductive data type consisting of terms built up from the 
following constructors:

  `const n`, a constant denoting the natural number n
  `var n`, a variable, numbered n
  `plus s t`, denoting the sum of s and t
  `times s t`, denoting the product of s and t
-/

inductive nat_term
| const : ℕ → nat_term
| var : ℕ → nat_term
| plus : nat_term → nat_term → nat_term
| times : nat_term → nat_term → nat_term

open nat_term

/-
Recursively define a function that evaluates any such term with respect to 
an assignment `val : ℕ → ℕ` of values to the variables.

For example, if `val 4 = 3
-/

def eval (val : ℕ → ℕ) : nat_term → ℕ
| (const k) := k
| (var k) := val k
| (plus s t) := (eval s) + (eval t)
| (times s t) := (eval s) * (eval t)

/-
Test it out by using #eval on some terms. You can use the following `val` function. In that case, for example, we would expect to have

  eval val (plus (const 2) (var 1)) = 5
-/

def val : ℕ → ℕ 
| 0 := 4
| 1 := 3
| 2 := 8
| _ := 0

example : eval val (plus (const 2) (var 1)) = 5 := rfl

#eval eval val (plus (const 2) (var 1))


/-
Below, we define a function `rev` that reverses a list. It uses an auxiliary function
`append1`. 

If you can, prove that the length of the list is preserved, and that
`rev (rev l) = l` for every `l`. The theorem below is given as an example, and should
be helpful. 

Note that when you use the equation compiler to define a function foo, `rw [foo]` uses
one of the defining equations if it can. For example, `rw [append1, ...]` in the theorem
uses the second equation in the definition of `append1`
-/

section

open list
variable {α : Type*}

def append1 (a : α) : list α → list α 
| nil      := [a]
| (b :: l) := b :: (append1 l)

def rev : list α → list α
| nil := nil
| (a :: l) := append1 a (rev l)

theorem length_append1 (a : α) (l : list α): length (append1 a l) = length l + 1 :=
sorry

theorem length_rev (l : list α) : length (rev l) = length l :=
sorry

lemma hd_rev (a : α) (l : list α) :
  a :: rev l =  rev (append1 a l) :=
sorry

theorem rev_rev (l : list α) : rev (rev l) = l :=
sorry

end
