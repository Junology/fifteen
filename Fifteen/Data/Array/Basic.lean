/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas

import Fifteen.Data.List.Basic

/-!
# Auxiliary lemmas about `Array`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u

namespace Array

variable {α : Type u}

theorem getElem_swap (as : Array α) (i j : Fin as.size) (k : Nat) {hk : k < (as.swap i j).size} : (as.swap i j)[k] = if j.1 = k then as[i.1] else if i.1 = k then as[j.1] else as[k]'(as.size_swap i j ▸ hk) := by
  have : ∀ {m n : Nat} (h : m = n) (i : Fin m), ((h ▸ i) : Fin n).val = i.val :=
    @fun
    | _, _, rfl, _ => rfl
  simp [swap, getElem_eq_data_get, List.get_set, this]

/-- The counterpart of `List.Nodup` in `Std` -/
def Nodup (as : Array α) : Prop :=
  as.data.Nodup

/--
`Array.ofFn f` is `Nodup` provided `f` is injective.

:::note warn
This lemma depends on `Classical.choice` since it uses `Array.getElem_ofFn`.
:::
-/
theorem nodup_ofFn {n : Nat} (f : Fin n → α) (hf : ∀ (i j : Fin n), f i = f j → i = j) : (Array.ofFn f).Nodup :=
  List.nodup_of_get_inj _ fun i j (hi : i < (ofFn f).size) (hj : j < (ofFn f).size) (h : (ofFn f)[i] = (ofFn f)[j]) => by
    simp only [Array.getElem_ofFn] at h
    cases hf _ _ h; rfl

theorem nodup_of_get_inj (as : Array α) (h : ∀ (i j : Nat) (hi : i < as.size) (hj : j < as.size), as[i] = as[j] → i = j) : as.Nodup :=
  List.nodup_of_get_inj as.data h

theorem Nodup.get_inj {as : Array α} (h : as.Nodup) (i j : Nat) (hi : i < as.size) (hj : j < as.size) : as[i] = as[j] → i = j :=
  List.Nodup.get_inj h (hi:=hi) (hj:=hj)

theorem nodup_swap (as : Array α) (i j : Fin as.size) (h : as.Nodup) : (as.swap i j).Nodup := by
  apply nodup_of_get_inj; intro k l hk hl has
  apply h.get_inj k l (as.size_swap i j ▸ hk) (as.size_swap i j ▸ hl)
  simp only [getElem_swap] at has
  rewrite [as.size_swap i j] at hk hl
  show as[k]'hk = as[l]'hl
  apply dite (j.val = k) <;> apply dite (i.val = k)
    <;> apply dite (j.val = l) <;> apply dite (i.val = l)
    <;> intro hil hjl hik hjk
  all_goals try (cases hik.symm.trans hil; rfl)
  all_goals try (cases hjk.symm.trans hjl; rfl)
  all_goals iterate rewrite [if_pos ‹_›] at has
  all_goals iterate rewrite [if_neg ‹_›] at has
  all_goals iterate rewrite [if_pos ‹_›] at has
  all_goals iterate rewrite [if_neg ‹_›] at has
  all_goals try cases ‹_ = k›
  all_goals try cases ‹_ = l›
  all_goals try simp [has]
  . simp only [← hik, has]
  . exfalso; exact hil <| h.get_inj _ _ _ _ has
  . exfalso; exact hjl <| h.get_inj _ _ _ _ has
  . simp only [hil]
  . exfalso; exact hik <| Eq.symm <| h.get_inj _ _ _ _ has
  . exfalso; exact hjk <| Eq.symm <| h.get_inj _ _ _ _ has

end Array

