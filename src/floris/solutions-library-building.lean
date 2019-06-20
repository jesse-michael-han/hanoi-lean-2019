
import algebra.pi_instances
set_option old_structure_cmd true

universe variables u
#print ring

class rng (α : Type u) extends add_comm_group α, semigroup α, distrib α

instance ring.to_rng {α} [h : ring α] : rng α :=
{..h}

variables {α : Type u} [rng α] {a b c x y z w : α} {n m : ℤ}

example : (x + y) * (z + w) = x * z + x * w + y * z + y * w :=
begin
  rw [right_distrib, left_distrib, left_distrib, ←add_assoc]
end

lemma rng.mul_zero [rng α] (a : α) : a * 0 = 0 :=
have a * 0 + 0 = a * 0 + a * 0, from calc
     a * 0 + 0 = a * (0 + 0)   : by simp
           ... = a * 0 + a * 0 : by rw left_distrib,
show a * 0 = 0, from (add_left_cancel this).symm

lemma rng.zero_mul [rng α] (a : α) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = (0 + 0) * a   : by simp
        ... = 0 * a + 0 * a : by rewrite right_distrib,
show 0 * a = 0, from  (add_left_cancel this).symm

instance rng.mul_zero_class : mul_zero_class α :=
{ zero_mul := rng.zero_mul,
  mul_zero := rng.mul_zero,
  .._inst_1 }

lemma rng.neg_mul_eq_mul_neg [s : rng α] (a b : α) : -(a * b) = a * -b :=
neg_eq_of_add_eq_zero begin rw [← left_distrib, add_right_neg, mul_zero] end

lemma rng.neg_mul_eq_neg_mul [s : rng α] (a b : α) : -(a * b) = -a * b :=
neg_eq_of_add_eq_zero begin rw [← right_distrib, add_right_neg, zero_mul] end

@[simp] lemma sub_neg : a * (b - c) = a * b - a * c :=
calc
   a * (b - c) = a * b + a * -c : left_distrib a b (-c)
           ... = a * b - a * c  : by simp [rng.neg_mul_eq_mul_neg]

@[simp] lemma rng.nat_smul_mul_left : ∀{n : ℕ}, n • a * b = n • (a * b)
| 0     := by simp
| (n+1) := by { simp [*, add_smul, right_distrib] }

@[simp] lemma rng.nat_smul_mul_right : ∀{n : ℕ}, a * n • b = n • (a * b)
| 0     := by simp
| (n+1) := by { simp [*, add_smul, left_distrib] }

@[simp] lemma rng.smul_mul_left : ∀{n : ℤ}, n • a * b = n • (a * b)
| (n : ℕ) := rng.nat_smul_mul_left
| -[1+n]  := show (-↑(n+1) : ℤ) • a * b  = (-↑(n+1) : ℤ) • (a * b),
  by { rw [neg_smul, neg_smul, ←rng.neg_mul_eq_neg_mul], congr' 1,
       apply rng.nat_smul_mul_left }

@[simp] lemma rng.smul_mul_right : ∀{n : ℤ}, a * n • b = n • (a * b)
| (n : ℕ) := rng.nat_smul_mul_right
| -[1+n]  := show a * (-↑(n+1) : ℤ) • b  = (-↑(n+1) : ℤ) • (a * b),
  by { rw [neg_smul, neg_smul, ←rng.neg_mul_eq_mul_neg], congr' 1,
       apply rng.nat_smul_mul_right }

@[simp] lemma smul_smul_comm : n • (m • a) = m • (n • a) :=
by simp [smul_smul, mul_comm]

def unitisation (α : Type u) : Type u := ℤ × α

namespace unitisation

instance : add_comm_group (unitisation α) :=
by { dsimp [unitisation], apply_instance }

instance : has_mul (unitisation α) :=
⟨λ ⟨(n : ℤ), a⟩ ⟨(m : ℤ), b⟩, ⟨n * m, n • b + m • a + a * b⟩⟩

@[simp] lemma mk_mul_mk : (⟨n, a⟩ * ⟨m, b⟩ : unitisation α) = ⟨n * m, n • b + m • a + a * b⟩ :=
rfl

@[simp] lemma mul_fst {x y : unitisation α} : (x * y).fst = x.fst * y.fst :=
by { cases x, cases y, refl }

@[simp] lemma mul_snd {x y : unitisation α} :
  (x * y).snd = x.fst • y.snd + y.fst • x.snd + x.snd * y.snd :=
by { cases x, cases y, refl }

instance : ring (unitisation α) :=
{ mul_assoc := λ ⟨n, a⟩ ⟨m, b⟩ ⟨k, c⟩,
  by { simp [mul_assoc], simp [mul_assoc, smul_smul, smul_add, mul_comm, right_distrib,  left_distrib] },
  one := ⟨1, 0⟩,
  one_mul := λ ⟨n, a⟩, by { simp },
  mul_one := λ ⟨n, a⟩, by { simp },
  left_distrib := λ ⟨n, a⟩ ⟨m, b⟩ ⟨k, c⟩,
  by { simp only, show _ * (_ + _) = _ + _, simp [left_distrib, add_smul, smul_add] },
  right_distrib := λ ⟨n, a⟩ ⟨m, b⟩ ⟨k, c⟩,
  by { simp only, show (_ + _) * _ = _ + _, simp [right_distrib, add_smul, smul_add] },
  ..prod.add_comm_group, ..unitisation.has_mul }


end unitisation

#print gpow
