/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.Fin.Basic

/-!
# Auxiliary lemmas about `List`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v

namespace List

variable {α : Type u} {β : Type v}

theorem getElem_mem (l : List α) (i : Nat) {hi : i < l.length} : l[i] ∈ l := by
  rewrite [getElem_eq_get]; exact l.get_mem i hi

theorem length_pmap {p : α → Prop} (f : (a : α) → p a → β) (l : List α) (h : ∀ a, a ∈ l → p a) : (l.pmap f h).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l IH => dsimp [pmap]; rw [IH]

theorem get_pmap {p : α → Prop} (f : (a : α) → p a → β) (l : List α) (h : ∀ a, a ∈ l → p a) (i : Fin (l.pmap f h).length) : (l.pmap f h).get i = f (l.get <| i.cast (l.length_pmap f h)) (h _ <| l.getElem_mem i) := by
  induction l with
  | nil => exact i.elim0
  | cons a l IH =>
    let ⟨i,hi⟩ := i
    cases i <;> dsimp; rfl
    exact IH _ _

theorem not_mem_erase_of_nodup [DecidableEq α] (a : α) {l : List α} (hnodup : l.Nodup) : a ∉ l.erase a := by
  induction l with
  | nil => intro h; cases h
  | cons b l IH =>
    dsimp [List.erase]
    have ⟨hhead, (htail : l.Nodup)⟩ := pairwise_cons.mp hnodup
    match hba : b == a with
    | true =>
      dsimp; cases of_decide_eq_true hba
      intro ha; exact hhead _ ha rfl
    | false =>
      dsimp; simp [not_or]
      apply And.intro
      . exact Ne.symm <| of_decide_eq_false hba
      . exact IH htail

theorem Nodup.erase [DecidableEq α] (a : α) {l : List α} (hnodup : l.Nodup) : (l.erase a).Nodup := by
  induction l with
  | nil => exact .nil
  | cons b l IH =>
    have ⟨hhead, (htail : l.Nodup)⟩ := pairwise_cons.mp hnodup
    dsimp [List.erase]
    match b == a with
    | true => dsimp; exact htail
    | false =>
      dsimp; refine pairwise_cons.mpr <| And.intro ?_ ?_
      . intro _ hb h; cases h
        exact hhead b (List.mem_of_mem_erase hb) rfl
      . exact IH htail

theorem nodup_cons_of_notmem_nodup (a : α) {l : List α} (ha : a ∉ l) (hnodup : l.Nodup) : (a :: l).Nodup := by
  refine .cons ?_ hnodup
  intros _ hal h; cases h
  exact ha hal

theorem nodup_of_nodup_map {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact .nil
  | cons a l IH =>
    dsimp at h
    have := pairwise_cons.mp h
    apply nodup_cons_of_notmem_nodup
    . intro ha; refine this.1 (f a) ?_ rfl
      exact List.mem_map_of_mem f ha
    . exact IH this.2

theorem nodup_of_get_inj (l : List α) (h : ∀ (i j : Nat) (_ : i < l.length) (_ : j < l.length), l[i] = l[j] → i = j) : l.Nodup := by
  induction l with
  | nil => exact .nil
  | cons a l IH =>
    refine .cons ?_ (IH fun i j hi hj hl => ?_)
    . intro _ hmem heq; cases heq
      have ⟨⟨i,hi⟩,hl⟩ := List.mem_iff_get.mp hmem
      have : i+1 = 0 :=
        h (i+1) 0 (Nat.succ_lt_succ hi) l.length.zero_lt_succ hl
      cases this
    . apply Nat.succ.inj
      exact h (i+1) (j+1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) hl

theorem Nodup.get_inj {l : List α} (nodup : l.Nodup) (i j : Nat) {hi : i < l.length} {hj : j < l.length} (h : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => cases hi
  | cons a l IH =>
    cases nodup with | cons ha nodup =>
    specialize IH nodup
    cases i <;> cases j <;> dsimp at h
    . rfl
    . exfalso
      suffices a ∈ l from ha a this rfl
      exact List.mem_iff_get.mpr ⟨_, h.symm⟩
    . exfalso
      suffices a ∈ l from ha a this rfl
      exact List.mem_iff_get.mpr ⟨_, h⟩
    . exact congrArg Nat.succ <| IH _ _ h

end List
