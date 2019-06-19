import topology.metric_space.basic

namespace playground

class my_add_semigroup (α : Type) :=
(add : α → α → α)
(add_assoc' : ∀ a b c, add (add a b) c = add a (add b c))
(add_comm' : ∀ a b, add a b = add b a)

section
open my_add_semigroup

theorem comm_assoc' {α : Type} [my_add_semigroup α] (a b c : α) :
  add (add a b) c = add c (add b a) :=
begin rw [add_comm' _ c, add_comm' b] end

--set_option old_structure_cmd true
class my_add_group (α : Type) extends my_add_semigroup α :=
(zero : α)
(add_zero' : ∀ a, add a zero = a)

#print my_add_group

open my_add_group

theorem zero_add' {α : Type} [my_add_group α] (a : α) :
  add (zero α) a = a :=
begin rw [add_comm', add_zero'] end


instance : my_add_semigroup ℕ :=
{ add := (+),
  add_assoc' := by intros; simp,
  add_comm' := by intros; simp }

theorem nat_comm_assoc (a b c : ℕ) : (a + b) + c = c + (b + a) :=
comm_assoc' a b c

set_option pp.all true
#print nat_comm_assoc
set_option pp.all false

theorem new_thm {α : Type} [my_add_group α] (a : α) :
  add a a = a :=
sorry

example (α : Type) [my_add_semigroup α] (a : α) : add a a = a :=
begin
  rw new_thm
end

end



#check topological_space
#check @continuous
#check metric_space

example (α : Type) [metric_space α] : continuous (λ x : α, x) :=
continuous_id


class t1 (α : Type) :=
(val1 : α)

class t2 (α : Type) :=
(val2 : ℕ)

class t3 (α : Type) :=
(val3 : α) (val4 : ℕ)

instance inst_t1_of_t3 (α : Type) [t3 α] : t1 α :=
{ val1 := t3.val3 α }

instance inst_t2_of_t3 (α : Type) [t3 α] : t2 α :=
{ val2 := t3.val4 α }

instance t3_int : t3 ℤ :=
{ val3 := -1, val4 := 100 }

#eval t1.val1 ℤ

/- instance inst_t3_of_t1_t2 (α : Type) [t1 α] [t2 α] : t3 α :=
{ val3 := t1.val1 α, val4 := t2.val2 α } -/

example (α : Type) [t1 α] [t2 α] : ℕ := t3.val4 α

set_option trace.class_instances true
example (α : Type) : ℕ := t3.val4 α
set_option trace.class_instances false




instance bad_instance (α β : Type) [has_add β] : t2 α :=
{ val2 := 5 }

set_option trace.class_instances true
#check t2.val2 ℕ
set_option trace.class_instances false

end playground

#check group
#check comm_group
#check ordered_comm_group
#check ring
#check field
#check discrete_field

#check fintype

#check decidable_eq


/-
  Exercise:
  Define a type class for your favorite kind of structure.
  Suggestions: monoids, groups, additive groups, rings, fields

  Define instances of your type class.
-/