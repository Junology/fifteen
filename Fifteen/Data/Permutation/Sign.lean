/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Data.Permutation.Basic

/-!
# Inversion and signs

Given a permutation `x : Permutation n` on `Fin n`, we call a pair `(i,j) : Fin n × Fin n` an ***inversion*** of `x` if `i < j` and `x[i] > x[j]`.
In this file, we discuss the inversions and the signs of permutations.

## Main declarations

* `Permutation.Inversion`: the structure representing each inversion.
* `Permutation.inversions`: the array of all inversions of a permutation.
* `Permutation.sign`: the sign of a permutation.

## TODO

* `(x * y).sign = (x.sign != y.sign)`
-/


namespace Permutation

variable {n : Nat}

/--
`Permutation.Inversion x` is a structure representing an inversion of given permutation `x : Permutation n`.

Recall that an ***inversion*** of `x` is a pair `(i,j) : Fin n × Fin n` such that `i < j` and `x[i] > x[j]`.
-/
structure Inversion (x : Permutation n) : Type where
  fst : Fin n
  snd : Fin n
  lt : fst < snd
  inverted : x[fst.1] > x[snd.1]
  deriving DecidableEq

namespace Inversion

instance (n : Nat) (x : Permutation n) : Repr (Inversion x) where
  reprPrec iv p := reprPrec (iv.fst, iv.snd) p

end Inversion


@[inline]
private def _root_.Nat.foldM' {α : Type u} {m : Type u → Type v} [Monad m] (k : Nat) (f : Fin k → α → m α) (init : α) : m α :=
  let rec @[specialize] loop : (i : Nat) → i ≤ k → α → m α
    | 0       , _, a => pure a
    | i'@(i+1), h, a =>
      have : k-i' < k := by
        cases ‹i' = i+1›; dsimp at h
        exact Nat.sub_lt (trans i.zero_lt_succ h) i.zero_lt_succ
      f ⟨k-i', this⟩ a >>= loop i (trans i.le_succ h)
  loop k .refl init

/-- Get the list of inversions of a permutation. -/
@[inline]
def inversions (x : Permutation n) : Array (Inversion x) :=
  #[] |> Nat.foldM' (m:=Id) n fun j ivs =>
    ivs |> Nat.foldM' j.1 fun i ivs =>
      if h : x[i.1]'(Nat.lt_trans i.2 j.2) > x[j.1] then
        ivs.push {
          fst := i.castLE (Nat.le_of_lt j.2)
          snd := j
          lt := i.2
          inverted := h
        }
      else
        ivs

/--
`Permutation.sign x` is the sign of the permutation `x : Permutation n`.
The function regards `Bool` as the group of order 2 by the XOR operation;
hence `Permutation.sign x = true` implies the parity is odd.
-/
@[inline]
def sign (x : Permutation n) : Bool :=
  x.inversions.size % 2 == 1

end Permutation