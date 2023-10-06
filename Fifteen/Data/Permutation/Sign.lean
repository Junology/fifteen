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

end Permutation
