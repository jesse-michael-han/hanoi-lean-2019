/-
Tactics in Lean are handled via the *tactic monad*. 
To write your own tactics, one needs to be familiar with the tactic monad and how it works. 
-/

import tactic.interactive

open tactic 

variables (a b c : Prop) 


/- In simple terms, tactics are programs which have return type `tactic α` for some type `α`. They act on the *tactic state*. 

Such programs go in between `begin ... end` blocks. 
-/
#check tactic 
#check intro 
#check exact
#check apply
#check cases 
#check repeat
#check target 

/-
Monads are an abstraction to emulate imperitive programming. As seen in the following example: (I)
-/

example : a → b → a ∧ b := 
begin
intros h₁ h₂, 
split, repeat {assumption},
end

example : a → b → a ∧ b := 
by do eh₁ ← intro `h₁,
      eh₂ ← intro `h₂, 
      split, 
      repeat assumption,
      trace_state 

def my_fun : list ℕ :=
do l ← [1,2,3],
   l ← [4,5,6],
  return (l+1)

example : a → b → a ∧ b :=
begin
intros ha hb,
exact (and.intro ha hb),
end

-- example : a → b → a ∧ b := 
-- by do eh₁ ← intro `h₁, 
--       eh₂ ← intro `h₂, 
--       e ← pure `(and.intro %%eh₁ %%eh₂),
--       exact e
      -- exact e 

/-
In the above, `expr`. `expr` is an inductive type which reflects internal representation of Lean expressions. During execution, the virtual machine replaces constructors of `expr` with their corresponding C++ internals and uses them during execution. 

Since `expr` is an inductive type, we can easily write functions to reason about them. (II)

* Show `expr`.
-/

meta def identify_conj : expr → tactic bool 
| `(%%a ∧ %%b) := pure tt 
|   e          := pure ff 


#check @list.mmap tactic _ expr expr 
#check infer_type 

meta def foo  : tactic unit := 
do ctx ← local_context,
   g ← @list.mmap tactic _ expr expr infer_type ctx,
  --  trace ctx,
  --  trace g,
   l ← g.mfilter identify_conj,
   trace l, 
   triv 

example (h₁ : a ∧ b) (h₂ : c → a) (h₃ : b ∧ c) : true  := by do foo 


/-
We can also add hypotheses to the local context. (III)
-/

example (h₁ : a) (h₂ : b) : true :=
by do hyp₁ ← get_local `h₁, 
      hyp₂ ← get_local `h₂, 
      typ₁ ← infer_type hyp₁, 
      typ₂ ← infer_type hyp₂,
      typ ← to_expr ``(%%typ₁ ∧ %%typ₂),
      trm ← to_expr ``(and.intro %%hyp₁ %%hyp₂),
      n ← get_unused_name `h, 
      assert n typ, exact trm,
      trace_state, triv 


/- 
The backticks: 

`foo is a way to refer to a name. 

``foo resolves foo at parse time. 

`( my_expr ) constructs an expression at parse time. 

``( my_pexpr ) constructs a pre-expression at parse time, resolves name in the current namespace of the tactic. 

```( my_pexpr ) constructs a pre-expression but defers name resolution to tactic runtime (`begin ... end` block of the user). 
-/

