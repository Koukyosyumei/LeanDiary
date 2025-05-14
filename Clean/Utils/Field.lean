import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

namespace FieldUtils
variable {p : ℕ} [p_prime: Fact p.Prime]

instance : NeZero p := ⟨p_prime.elim.ne_zero⟩

theorem p_neq_zero : p ≠ 0 := p_prime.elim.ne_zero

theorem ext {x y : F p} (h : x.val = y.val) : x = y := by
  cases p; cases p_neq_zero rfl
  exact Fin.ext h

theorem sum_do_not_wrap_around (x y: F p) :
  x.val + y.val < p -> (x + y).val = x.val + y.val := by
  intro h
  have sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val :=
    (Nat.mod_eq_iff_lt p_neq_zero).mpr h
  rw [ZMod.val_add]
  rw [sum_eq_over_naturals]

theorem byte_sum_do_not_wrap (x y : F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> (x + y).val = x.val + y.val := by
  intros hx hy
  have sum_lt_512 : x.val + y.val < 512 := Nat.add_lt_add hx hy
  have sum_lt_p : x.val + y.val < p := Nat.lt_trans sum_lt_512 p_large_enough.elim
  apply sum_do_not_wrap_around x y
  exact sum_lt_p

theorem byte_sum_le_bound (x y : F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> (x + y).val < 511 := by
  intros hx hy
  apply Nat.le_sub_one_of_lt at hx
  apply Nat.le_sub_one_of_lt at hy
  have sum_bound := Nat.add_le_add hx hy
  simp at sum_bound
  apply Nat.lt_add_one_of_le at sum_bound
  rw [ZMod.val_add]
  simp at sum_bound
  have tmp: 511 < 512 := by {simp}
  have val_511_lt_p : 511 < p := Nat.lt_trans tmp p_large_enough.elim
  have sum_le_p : (x.val + y.val) < p := Nat.lt_trans sum_bound val_511_lt_p
  have sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val
    := (Nat.mod_eq_iff_lt p_neq_zero).mpr sum_le_p
  rw [sum_eq_over_naturals]
  exact sum_bound

theorem byte_sum_and_bit_do_not_wrap (x y b : F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> b.val < 2 -> (b + x + y).val = b.val + x.val + y.val := by
  intros hx hy hb
  have sum_bound := byte_sum_le_bound x y hx hy
  have sum_lt_512 : b.val + (x + y).val ≤ 511 := by
    apply Nat.le_sub_one_of_lt at sum_bound
    apply Nat.le_sub_one_of_lt at hb
    simp at sum_bound
    simp at hb
    apply Nat.add_le_add hb sum_bound
  have sum_lt_512' : b.val + (x + y).val < 512 := by {
    apply Nat.lt_add_one_of_le at sum_lt_512
    simp at sum_lt_512
    exact sum_lt_512
  }
  have sum_lt_p: b.val + (x + y).val < p := Nat.lt_trans sum_lt_512' p_large_enough.elim
  rw [add_assoc, sum_do_not_wrap_around b (x + y) sum_lt_p,
    byte_sum_do_not_wrap x y hx hy, ←add_assoc]
