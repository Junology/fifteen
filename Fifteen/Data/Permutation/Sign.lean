/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Logic.BishopFin
import Fifteen.Data.Nat.Basic
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

/-- Get the list of inversions of a permutation. -/
@[inline]
def inversions (x : Permutation n) : Array (Inversion x) :=
  #[] |> Nat.fold' n fun j ivs =>
    ivs |> Nat.fold' j.1 fun i ivs =>
      if h : x[i.1]'(Nat.lt_trans i.2 j.2) > x[j.1] then
        ivs.push {
          fst := i.castLE (Nat.le_of_lt j.2)
          snd := j
          lt := i.2
          inverted := h
        }
      else
        ivs

theorem mem_inversions (x : Permutation n) (iv : Inversion x) : iv ∈ x.inversions := by
  let ⟨i,j,hlt,hinv⟩ := iv
  dsimp [inversions]
  refine Nat.fold'_induction (motive := fun k (ivs : Array (Inversion x)) => j.1 < k → ⟨i,j,hlt,hinv⟩ ∈ ivs) n _ #[] ?zero ?succ j.2
  all_goals simp
  . intro hj; cases hj
  . intro k hk invs IH hjk
    have : i.1 < k := trans (r:=LT.lt (α:=Nat)) hlt (Nat.le_of_succ_le_succ hjk)
    refine Nat.fold'_induction (motive := fun l (ivs' : Array (Inversion x)) => (i.1 < l ∨ j.1 < k) → ⟨i,j,hlt,hinv⟩ ∈ ivs') k _ invs ?_ ?_ (Or.inl this)
    all_goals simp
    . intro hi
      cases hi with
      | inl hi => cases hi
      | inr hj => exact IH hj
    . intro l hl invs' IH' hil
      cases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hjk) with
      | inl heq =>
        cases heq
        have : i.1 ≤ l :=
          Nat.le_of_succ_le_succ (Or.resolve_right hil j.1.lt_irrefl)
        cases Nat.eq_or_lt_of_le this with
        | inl heq =>
          cases heq; rewrite [dif_pos hinv]
          exact Array.mem_push.mpr <| Or.inr rfl
        | inr hlt =>
          specialize IH' (Or.inl hlt)
          if hx : x[l]'(Nat.lt_trans hl j.2) > x[j.1] then
            rewrite [dif_pos hx]
            exact Array.mem_push.mpr <| Or.inl IH'
          else
            rewrite [dif_neg hx]; exact IH'
      | inr hlt =>
        specialize IH' (Or.inr hlt)
        if hx : x[l]'(Nat.lt_trans hl hk) > x[k]'hk then
          rewrite [dif_pos hx]
          exact Array.mem_push.mpr <| Or.inl IH'
        else
          rewrite [dif_neg hx]; exact IH'

theorem nodup_inversions (x : Permutation n) : x.inversions.Nodup := by
  suffices x.inversions.Nodup ∧ ∀ iv, iv ∈ x.inversions → iv.snd.1 < n
  from this.1
  dsimp [inversions]
  refine Nat.fold'_induction (motive := fun k (ivs : Array (Inversion x)) => ivs.Nodup ∧ ∀ iv, iv ∈ ivs → iv.snd.1 < k) n _ #[] ?_ ?_
  all_goals simp
  . exact ⟨.nil, fun _ h => nomatch h⟩
  . intro k hk ivs ivs_nodup ivs_lt
    generalize hivs' : Nat.fold' k _ ivs = ivs'
    suffices Array.Nodup ivs' ∧ ∀ iv, iv ∈ ivs' → iv.snd.1 < k ∨ (iv.snd.1 = k ∧ iv.fst.1 < k) by
      refine And.imp_right ?_ this
      intro hivs' iv hiv
      apply Nat.succ_le_succ; apply Nat.le_iff_lt_or_eq.mpr
      exact Or.imp_right And.left (hivs' iv hiv)
    cases hivs'
    refine Nat.fold'_induction (motive := fun l (ivs' : Array (Inversion x)) => ivs'.Nodup ∧ ∀ iv, iv ∈ ivs' → iv.snd.1 < k ∨ (iv.snd.1 = k ∧ iv.fst.1 < l)) k _ ivs ?_ ?_
    all_goals simp
    . exact And.intro ivs_nodup fun iv hiv => Or.inl <| ivs_lt iv hiv
    . intro l hl ivs' ivs'_nodup ivs'_lt
      if hx : x[l]'(Nat.lt_trans hl hk) > x[k] then
        simp only [dif_pos hx, Array.nodup_push, Array.mem_push, ivs'_nodup, true_and]
        constructor
        . intro h
          specialize ivs'_lt _ h; dsimp at ivs'_lt
          refine ivs'_lt.elim ?_ ?_
          . exact Nat.lt_irrefl k
          . intro h; exact Nat.lt_irrefl l h.2
        . intro iv hiv
          cases hiv with
          | inl hmem =>
            refine Or.imp_right ?_ <| ivs'_lt iv hmem
            exact And.imp_right Nat.le.step
          | inr heq =>
            cases heq; dsimp
            exact Or.inr ⟨rfl, l.lt_succ_self⟩
      else
        simp only [dif_neg hx]
        apply And.intro ivs'_nodup
        intro iv hiv; specialize ivs'_lt iv hiv
        refine Or.imp_right ?_ ivs'_lt
        exact And.imp_right Nat.le.step

instance Inversion.finite (x : Permutation n) : BishopFin (Inversion x) where
  elems' := x.inversions.toList
  nodup_elems' := by
    rewrite [Array.toList_eq]; exact x.nodup_inversions
  mem_elems' := by
    simp only [Array.toList_eq, ← Array.mem_iff_mem_data]
    exact x.mem_inversions

/--
`Permutation.sign x` is the sign of the permutation `x : Permutation n`.
The function regards `Bool` as the group of order 2 by the XOR operation;
hence `Permutation.sign x = true` implies the parity is odd.
-/
@[inline]
def sign (x : Permutation n) : Bool :=
  x.inversions.size % 2 == 1

end Permutation