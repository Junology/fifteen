/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Data.Permutation.Inversion

/-!
# Signs of permutations

For a permutation `x`, its ***parity*** is defined in the following mutually equvlent ways:

* the parity of the number of transpositions which `x` factors as;
* the parity of the number of ***inversions*** of `x`;
* the parity of the Young diagram associated with `x`.

In this file, we define `Permutation.sign` based on the second definition.

## Main declarations and results

* `Permutation.sign`: the sign of a permutation.
* `Permutation.sign_mul`: multiplicativity of `Permutation.sign`.

-/

set_option autoImplicit false

universe u


namespace Permutation

variable {m n : Nat}

/-! ### Declarations about `Permutation.sign` -/

/--
`Permutation.sign x` is the sign of the permutation `x : Permutation n`.
The function regards `Bool` as the group of order 2 by the XOR operation;
hence `Permutation.sign x = true` implies the parity is odd.
-/
@[inline]
def sign (x : Permutation n) : Bool :=
  x.inversionNum % 2 == 1

theorem sign_one : (1 : Permutation n).sign = false := by
  dsimp [sign]
  rewrite [inversionNum_one]
  decide

/--
Multiplicativity of `Permutation.sign`.

:::note warn
The theorem depends on `Classicla.choice` since `Permutation.inversionNum_add` does.
:::
-/
@[simp]
theorem sign_mul (x y : Permutation n) : (x * y).sign = (x.sign != y.sign) := by
  have := congrArg (· % 2) <| inversionNum_add x y
  conv at this =>
    dsimp; rw [Nat.add_mul_mod_self_left, Nat.add_mod]
  dsimp [sign]; rw [← this]; clear this
  generalize x.inversionNum = m
  generalize y.inversionNum = n
  cases m.mod_two_eq_zero_or_one
    <;> cases n.mod_two_eq_zero_or_one
    <;> rename_i hm hn
    <;> simp only [hm, hn]

@[simp]
theorem sign_inv (x : Permutation n) : x.inv.sign = x.sign := by
  have : sign (x.inv * x) = sign (1 : Permutation n) := x.inv_mul ▸ rfl
  conv at this =>
    simp only [sign_mul, sign_one]
    rewrite [Bool.bne_eq_false]
  exact this

theorem sign_powNat_of_even (x : Permutation n) (k : Nat) (h : x.sign = false) : (x^k).sign = false := by
  induction k with
  | zero => rw [powNat_zero, sign_one]
  | succ k IH =>
    rewrite [powNat_succ, sign_mul, h, IH]
    decide

theorem sign_powInt_of_even (x : Permutation n) (k : Int) (h : x.sign = false) : (x^k).sign = false := by
  rcases k with ⟨k⟩ | ⟨k⟩
  . show sign (x ^ (k : Nat)) = false
    exact sign_powNat_of_even x k h
  . show sign (x.inv ^ (k+1 : Nat)) = false
    apply sign_powNat_of_even
    rewrite [x.sign_inv]
    exact h

@[simp]
theorem sign_conj (x y : Permutation n) : (x * y * x.inv).sign = y.sign := by
  simp only [sign_mul]
  rw [sign_inv, Bool.bne_comm x.sign, Bool.bne_assoc, Bool.bne_self, Bool.bne_false]

@[simp]
theorem sign_transposAdj (i : Nat) (h : i+1 < n) : (transposAdj i h).sign = true := by
  dsimp [sign]
  rewrite [inversionNum_transposAdj]
  decide

@[simp]
theorem sign_transpos (i j : Fin n) (h : i ≠ j) : (transpos i j).sign = true := by
  suffices ∀ (i j : Fin n), i < j → (transpos i j).sign = true by
    rcases Nat.lt_trichotomy i.1 j.1 with hlt | heq | hgt
    . exact this i j hlt
    . exfalso; exact h <| Fin.eq_of_val_eq heq
    . rewrite [transpos_comm]; exact this j i hgt
  clear i j h; intro i j h
  rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
  simp at h
  induction h with
  | refl => exact sign_transposAdj i hj
  | @step j hij IH =>
    let s := transpos ⟨i,hi⟩ ⟨j, Nat.lt_of_succ_lt hj⟩
    have : transpos ⟨i,hi⟩ ⟨j+1,hj⟩ = transposAdj j hj * s * (transposAdj j hj).inv := by
      simp only [transpos_conj]
      rw [get_transposAdj_of_lt hij, get_transposAdj_self]
    rewrite [this]; simp only [sign_conj]
    exact IH _

@[simp]
theorem sign_swap (x : Permutation n) (i j : Fin n) (h : i ≠ j) : (x.swap i j).sign = !x.sign := by
  rewrite [← mul_transpose_eq_swap, sign_mul, sign_transpos i j h]
  exact Bool.bne_true _

/-- The sign of the cyclic permutation defined by a non-empty list, say `(i :: l) : List (Fin n)`, equals the parity of the length of the tail `l` provided `i ∉ l`. -/
theorem sign_cyclic_cons {n : Nat} {i : Fin n} {l : List (Fin n)} (h : i ∉ l) : (cyclic (i :: l)).sign = (l.length % 2 == 1) := by
  dsimp [cyclic]
  induction l with
  | nil => exact sign_one
  | cons j l IH =>
    dsimp
    rewrite [List.mem_cons, not_or] at h
    rewrite [sign_swap _ i j h.1, IH h.2, Bool.eq_iff_iff]
    conv =>
      lhs; rewrite [Nat.not_beq_eq_true_eq]
    conv =>
      rhs; rewrite [beq_iff_eq, Nat.succ_eq_add_one, Nat.add_mod]
      change (l.length % 2 + 1) % 2 = 1
    cases l.length.mod_two_eq_zero_or_one
    all_goals (rename_i h; simp only [h])

end Permutation
