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

universe u v

namespace Array

variable {α : Type u}

/--
:::note warn
This theorem depends on `Classical.choice` since `Array.append_data` does.
:::
-/
theorem size_append (as bs : Array α) : (as ++ bs).size = as.size + bs.size := by
  dsimp [size]; rw [append_data, List.length_append]

theorem getElem_swap (as : Array α) (i j : Fin as.size) (k : Nat) {hk : k < (as.swap i j).size} : (as.swap i j)[k] = if j.1 = k then as[i.1] else if i.1 = k then as[j.1] else as[k]'(as.size_swap i j ▸ hk) := by
  have : ∀ {m n : Nat} (h : m = n) (i : Fin m), ((h ▸ i) : Fin n).val = i.val :=
    @fun
    | _, _, rfl, _ => rfl
  simp [swap, getElem_eq_data_get, List.get_set, this]

/--
:::note warn
This theorem depends on `Classical.choice` since `Array.append_data` does.
:::
-/
theorem getElem_append_left {i : Nat} (as bs : Array α) (h : i < as.size) {h' : i < (as ++ bs).size} : (as ++ bs)[i] = as[i] := by
  rewrite [getElem_eq_data_get]
  rewrite [List.get_of_eq (Array.append_data as bs)]
  rewrite [List.get_append_left as.data bs.data h]
  rfl

/--
:::note warn
This theorem depends on `Classical.choice` since `Array.append_data` does.
:::
-/
theorem getElem_append_right {i : Nat} (as bs : Array α) (h : i ≥ as.size) {h' : i < (as ++ bs).size} : (as ++ bs)[i] = bs[i-as.size]'(Nat.sub_lt_left_of_lt_add h (Array.size_append as bs ▸ h')) := by
  rewrite [getElem_eq_data_get]
  rewrite [List.get_of_eq (Array.append_data as bs)]
  rewrite [List.get_append_right' h]
  rfl

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

/--
:::note warn
The lemma depends on `Classical.choice` since `Array.getElem_append_left`, `Array.getElem_append_right`, and etc do.
:::
-/
theorem nodup_append {as bs : Array α} (has : as.Nodup) (hbs : bs.Nodup) (hdisj : ∀ (i j : Nat) (hi : i < as.size) (hj : j < bs.size), as[i] ≠ bs[j]) : (as ++ bs).Nodup :=
  nodup_of_get_inj _ fun i j hi hj => by
    if hi' : i < as.size then
      rewrite [getElem_append_left as bs hi']
      if hj' : j < as.size then
        rewrite [getElem_append_left as bs hj']
        exact has.get_inj i j hi' hj'
      else
        rewrite [getElem_append_right as bs (Nat.le_of_not_lt hj')]
        intro hij; exfalso
        exact hdisj _ _ _ _ hij
    else
      have hi'' : i ≥ as.size := Nat.le_of_not_lt hi'
      have : i - as.size < bs.size :=
        Nat.sub_lt_left_of_lt_add hi'' (size_append _ _ ▸ hi)
      rewrite [getElem_append_right as bs (Nat.le_of_not_lt hi')]
      if hj' : j < as.size then
        rewrite [getElem_append_left as bs hj']
        intro hij; exfalso
        exact hdisj _ _ _ _ hij.symm
      else
        have hj'' : j ≥ as.size := Nat.le_of_not_lt hj'
        have : j - as.size < bs.size :=
          Nat.sub_lt_left_of_lt_add hj'' (size_append _ _ ▸ hj)
        rewrite [getElem_append_right as bs (Nat.le_of_not_lt hj')]
        intro h
        have := hbs.get_inj (i-as.size) (j-as.size) ‹_› ‹_› h
        conv at this =>
          rewrite [Nat.sub_eq_iff_eq_add hi'']
          rewrite [Nat.sub_add_cancel hj'']
        exact this

/--
:::note warn
The lemma depends on `Classical.choice` since `Array.getElem_map` does.
:::
-/
theorem nodup_map {β : Type v} (f : α → β) (as : Array α) (has : as.Nodup) (hf : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) : (as.map f).Nodup :=
  nodup_of_get_inj _ fun i j hi hj h => by
    conv at h =>
      simp only [Array.getElem_map]
    apply has.get_inj; apply hf _ _ h

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

