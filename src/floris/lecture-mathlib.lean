/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn.

A lecture on mathlib.
-/
import data.rat.basic tactic.norm_num

/-
  You can find mathlib at https://github.com/leanprover-community/mathlib/

  It was started in July 2017 to separate the mathematics library from the core library.
  The core library is part on Lean: https://github.com/leanprover/lean/tree/master/library

  Initially the main developer of mathlib was Mario Carneiro

  Currently, has 9 maintainers: Jeremy Avigad, Reid Barton, Mario Carneiro, Johan Commelin,
  Sébastien Gouëzel, Simon Hudon, Chris Hughes, Robert Y. Lewis and Patrick Massot.
-/

/-
  Contents
  * Data -- number systems, sets, equiv (bijections), lists, polynomials and much more
  * Algebra -- mostly equations and basic lemmas, some instances
    * Group Theory
    * Ring Theory
    * Field Theory
    * Linear Algebra
    * Order
  * Analysis -- still lacking, has Frechet derivative, Lebesque integral (mostly), but not much theorems about either, and also not specialized to special cases
    * Topology
    * Measure Theory
  * Number Theory -- very little content
  * Logic -- basic logic, much of it is also in core
    * Category Theory
    * Set Theory -- cardinal and ordinal numbers
  * Meta(programming)
    * Tactics -- many useful tactics are defined here
    * Category -- do not confuse with category theory.
-/

/-
  Navigating mathlib
  * "Go to definition" and "peek definition"
  * Browse through files
  * Search in VSCode
  * Search on Github
  * Potentially: `#print prefix` and `#print instances`
-/
-- useful: alt+left (option+cmd+left on Mac) to jump to previous location
-- or use ctrl+tab (option+cmd+tab on Mac) to navigate between VSCode tabs.
#print is_group_hom
#check tactic.assumption
#print prefix nat
#print instances group


/-
  Use the command `update-mathlib` to download compiled version of mathlib.

  To get this command,
  * make sure you have Python installed
  * Now in a terminal (on Windows use `git bash`), type:
  ```
    curl https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/remote-install-update-mathlib.sh -sSf | bash
  ```
  * For more information, see
    https://github.com/leanprover-community/mathlib/tree/master/docs/install
-/

/-
  If you want to make a new project depending on mathlib, you can execute (in a command line)
  ```
    mkdir my_project
    cd my_project
    leanpkg init my_project
    leanpkg add leanprover-community/mathlib
    update-mathlib
  ```
  If you clone a repository (assuming it already has a leanpkg.toml file):
  ```
    git clone https://www.github.com/<username>/<project>
    cd <project>
    leanpkg configure
    update-mathlib
  ```
  To update mathlib, run
  ```
    leanpkg upgrade
    update-mathlib
  ```
-/

/-
  Contributing to mathlib:
  https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/index.md
  * Use Zulip to discuss your contribution before and while you are working on it.
    https://leanprover.zulipchat.com/
  * If you are done, make a pull request on Github. After that it will be reviewed.
-/

/- If `e : t` then `e.foo` is the same as `t.foo e`-/
example (n m : ℕ) : nat.gcd n m = n.gcd m :=
by reflexivity

lemma mul_eq_mul_left {α} [integral_domain α] {a b c : α} (ha : a ≠ 0) :
  a * b = a * c ↔ b = c :=
⟨eq_of_mul_eq_mul_left ha, λ h, by rw h⟩

open rat
local infix ` /. `:70 := mk
lemma rat.coe_num_eq_iff (r : ℚ) :
  (r.num : ℚ) = r ↔ r.denom = 1 :=
begin
  rw [coe_int_eq_mk],
  conv { to_lhs, to_rhs, rw [num_denom r] },
  rw [mk_eq],
  { by_cases h : r.num = 0,
    { simpa [h] using r.cop },
    { rw [mul_eq_mul_left h], norm_cast }
   },
   norm_num,
   simpa using r.denom_ne_zero
end
