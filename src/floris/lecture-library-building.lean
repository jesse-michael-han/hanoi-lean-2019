/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn.

A lecture on library-building.
-/
import algebra.group

set_option old_structure_cmd true
universe variable u

/-
  Techniques:
-/

/-
  Use good names: https://github.com/leanprover-community/mathlib/blob/master/docs/contribute/naming.md
-/

#print nat.succ_ne_zero
#print mul_zero
#print mul_one

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
