/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.List.Count
import Std.Data.Fin.Basic

import Fifteen.Logic.Basic

/-!
# Auxiliary lemmas about `List`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v

namespace List

variable {α : Type u} {β : Type v}

/-! ### Lemmas about length -/

theorem length_pmap {p : α → Prop} (f : (a : α) → p a → β) (l : List α) (h : ∀ a, a ∈ l → p a) : (l.pmap f h).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l IH => dsimp [pmap]; rw [IH]

theorem Nodup.length_le_of_subset {l l₁ : List α} (nodup : l.Nodup) (h : Subset l l₁) : l.length ≤ l₁.length := by
  induction l generalizing l₁ with
  | nil => exact l₁.length.zero_le
  | cons a l IH =>
    have .cons nodup_head (nodup_tail : l.Nodup) := nodup
    let ⟨ha,hl⟩ := cons_subset.mp h
    clear nodup h
    have ⟨l₁', l₁'', hl₁⟩ := mem_iff_append.mp ha
    cases hl₁; clear ha
    have : l ⊆ l₁' ++ l₁'' := fun b hb => 
      match mem_append.mp (hl hb) with
      | .inl hb => mem_append.mpr <| Or.inl hb
      | .inr hb => mem_append.mpr <| Or.inr <|
        match hb with
        | .head _ => absurd rfl <| nodup_head b ‹b ∈ l›
        | .tail _ h => h
    specialize IH nodup_tail this
    simp only [length_append, length_cons] at IH ⊢
    exact Nat.succ_le_succ IH


/-! ### Declarations about `List.mem` or `Membership.mem` -/

theorem mem_cons_iff_of_mem {l : List α} {a b : α} (hb : b ∈ l) : a ∈ b :: l ↔ a ∈ l := by
  simp only [mem_cons, or_iff_right_iff_imp]; intro heq; exact heq ▸ hb

theorem getElem_mem (l : List α) (i : Nat) {hi : i < l.length} : l[i] ∈ l := by
  rewrite [getElem_eq_get]; exact l.get_mem i hi

theorem get_pmap {p : α → Prop} (f : (a : α) → p a → β) (l : List α) (h : ∀ a, a ∈ l → p a) (i : Fin (l.pmap f h).length) : (l.pmap f h).get i = f (l.get <| i.cast (l.length_pmap f h)) (h _ <| l.getElem_mem i) := by
  induction l with
  | nil => exact i.elim0
  | cons a l IH =>
    let ⟨i,hi⟩ := i
    cases i <;> dsimp; rfl
    exact IH _ _

theorem mem_pmap {p : α → Prop} {b : β} {f : (a : α) → p a → β} {l : List α} {hp : ∀ a, a ∈ l → p a} : b ∈ l.pmap f hp ↔ ∃ a h, (a ∈ l ∧ b = f a h) := by
  induction l with
  | nil => simp
  | cons a l IH =>
    dsimp [pmap]
    simp only [mem_cons, exists_and_left, exists_eq_or_imp, IH]
    apply or_congr_left
    constructor
    . intro h; exact .intro _ h
    . intro h; cases h; assumption

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


/-! ### Lemmas about `List.Nodup` -/

theorem Nodup.tail {a : α} {l : List α} (h : Nodup (a :: l)) : Nodup l :=
  match h with | .cons _ h => h

theorem Nodup.head {a : α} {l : List α} (h : Nodup (a :: l)) : a ∉ l :=
  match h with
  | .cons h _ => fun hmem => h a hmem rfl

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

theorem nodup_singleton (a : α) : [a].Nodup :=
  .cons (fun _ h => nomatch h) .nil

theorem nodup_cons_of_notmem_nodup (a : α) {l : List α} (ha : a ∉ l) (hnodup : l.Nodup) : (a :: l).Nodup := by
  refine .cons ?_ hnodup
  intros _ hal h; cases h
  exact ha hal

theorem nodup_range' (start len step : Nat) (hstep : step > 0) : (range' start len step).Nodup := by
  induction len generalizing start with
  | zero => exact .nil
  | succ len IH =>
    refine Pairwise.cons ?_ (IH _)
    intro n hn; let ⟨k,hk⟩ := mem_range'.mp hn
    suffices start < n from Nat.ne_of_lt this
    calc start
      _ < start + step := Nat.lt_add_of_pos_right hstep
      _ ≤ start + step + step * k := Nat.le_add_right ..
      _ = n := hk.2.symm

theorem nodup_range (n : Nat) : (range n).Nodup := by
  rewrite [range_eq_range']
  apply nodup_range'; decide

theorem nodup_of_nodup_map {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact .nil
  | cons a l IH =>
    dsimp at h
    apply nodup_cons_of_notmem_nodup
    . intro ha; exact h.head <| List.mem_map_of_mem f ha
    . exact IH h.tail

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

theorem Nodup.filter {l : List α} (nodup : l.Nodup) (p : α → Bool) : (l.filter p).Nodup := by
  induction l with
  | nil => exact .nil
  | cons a l IH =>
    specialize IH nodup.tail
    dsimp [List.filter]
    cases p a <;> dsimp
    . exact IH
    . refine nodup_cons_of_notmem_nodup _ ?_ IH
      intro ha
      exact nodup.head <| l.filter_sublist.subset ha

theorem Nodup.map {l : List α} (nodup : l.Nodup) (f : α → β) (hf : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) : (l.map f).Nodup := by
  apply nodup_of_get_inj
  intro i j hi hj
  simp only [getElem_eq_get, get_map]
  intro hfij; specialize hf _ _ hfij
  exact nodup.get_inj i j hf

theorem Nodup.pmap {p : α → Prop} {l : List α} (nodup : l.Nodup) (f : (a : α) → p a → β) (h : ∀ a, a ∈ l → p a) (f_inj : ∀ (a₁ a₂ : α) (h₁ : p a₁) (h₂ : p a₂), f a₁ h₁ = f a₂ h₂ → a₁ = a₂) : (l.pmap f h).Nodup := by
  apply nodup_of_get_inj
  intro i j hi hj
  simp only [getElem_eq_get, get_pmap]
  intro hfij; specialize f_inj _ _ _ _ hfij
  exact nodup.get_inj i j f_inj

theorem Nodup.append {l l' : List α} (nodup : l.Nodup) (nodup' : l'.Nodup) (h : ∀ a, a ∈ l → a ∉ l') : (l ++ l').Nodup := by
  induction l with
  | nil => exact nodup'
  | cons a l IH =>
    specialize IH nodup.tail fun a ha =>
      h a <| mem_cons_of_mem _ ha
    refine nodup_cons_of_notmem_nodup a ?_ IH
    simp only [append_eq, mem_append, not_or]
    exact ⟨nodup.head, h a <| l.mem_cons_self a⟩

theorem Nodup.product {la : List α} {lb : List β} (la_nodup : la.Nodup) (lb_nodup : lb.Nodup) : (la.product lb).Nodup := by
  induction la with
  | nil => exact .nil
  | cons a la IH =>
    specialize IH la_nodup.tail
    conv =>
      arg 1
      dsimp [List.product, List.bind]
      change lb.map (Prod.mk a) ++ la.product lb
    refine Nodup.append ?_ IH ?_
    . apply lb_nodup.map
      intro b₁ b₂; exact congrArg Prod.snd
    . intro x
      let ⟨_,b⟩ := x
      simp only [mem_map, Prod.mk.injEq, exists_eq_right_right, and_imp, pair_mem_product]
      intro _ ha h; cases ha
      exact la_nodup.head h.1


/-! ### Lemmas about `List.countP` -/

theorem countP_erase_true [DecidableEq α] {p : α → Bool} {l : List α} {a : α} (ha : a ∈ l) (hp : p a = true) : l.countP p = (l.erase a).countP p + 1 := by
  induction l with
  | nil => cases ha
  | cons a' l IH =>
    rewrite [List.erase_cons]
    if h : a' = a then
      cases h; simp only [if_pos, countP_cons, if_pos hp]
    else
      simp only [countP_cons, if_neg h]
      rewrite [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc]
      apply congrArg (· + _)
      exact IH <| (mem_cons.mp ha).resolve_left (Ne.symm h)

theorem countP_erase_false [DecidableEq α] {p : α → Bool} {l : List α} {a : α} (ha : a ∈ l) (hp : p a = false) : l.countP p = (l.erase a).countP p := by
  induction l with
  | nil => cases ha
  | cons a' l IH =>
    rewrite [List.erase_cons]
    if h : a' = a then
      cases h; simp only [if_true, countP_cons, hp, if_neg, Nat.add_zero]
    else
      simp only [countP_cons, if_neg h]
      apply congrArg (· + _)
      exact IH <| (mem_cons.mp ha).resolve_left (Ne.symm h)

theorem countP_le_one_of_unique_nodup {p : α → Bool} {l : List α} (hp : ∀ a b, p a = true → p b = true → a = b) (hl : l.Nodup) : l.countP p ≤ 1 := by
  induction l with
  | nil => exact .step .refl
  | cons a l IH =>
    simp only [countP_cons]
    cases Nat.eq_or_lt_of_le (IH hl.tail) with
    | inl hone =>
      have ⟨b,hb⟩:= (countP_pos p).mp (trans Nat.zero_lt_one hone.symm)
      rewrite [hone, Nat.add_comm]
      apply Nat.succ_le_succ
      if hpa : p a = true then
        have : a = b := hp _ _ hpa hb.2
        cases this
        exact absurd hb.1 hl.head
      else
        rewrite [if_neg hpa]; exact .refl
    | inr hlt =>
      have := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hlt)
      rewrite [this, Nat.zero_add]
      cases p a <;> decide

theorem countP_or_le_add {p q : α → Bool} {l : List α} : l.countP (fun a => p a || q a) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => exact .refl
  | cons a l IH =>
    simp only [countP_cons]
    cases p a <;> cases q a <;> simp only [ite_true, ite_false, Nat.add_zero]
    . exact IH
    . exact Nat.succ_le_succ IH
    . rewrite [Nat.succ_add]; exact Nat.succ_le_succ IH
    . rewrite [Nat.succ_add]; exact Nat.succ_le_succ <| .step IH

theorem countP_disjoint {p q : α → Bool} {l : List α} (h : ∀ a, (p a && q a) = false) : l.countP (fun a => p a || q a) = l.countP p + l.countP q := by
  induction l with
  | nil => exact (Nat.zero_add 0).symm
  | cons a l IH =>
    simp only [countP_cons]
    specialize h a; revert h
    cases p a <;> cases q a <;> simp [IH]
    . rw [Nat.add_assoc]
    . rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc]

theorem countP_image_le_length [DecidableEq β] {la : List α} {lb : List β} (hnodup : lb.Nodup) (f : α → β) : lb.countP (fun b => decide <| ∃ a, a ∈ la ∧ f a = b) ≤ la.length := by
  induction la with
  | nil => simp
  | cons a la IH =>
    simp only [mem_cons, exists_eq_or_imp, decide_or]
    refine trans (s:=LE.le) countP_or_le_add ?_
    rewrite [length_cons, Nat.succ_eq_one_add]
    refine Nat.add_le_add ?_ IH
    refine countP_le_one_of_unique_nodup ?_ hnodup
    intro b₁ b₂ hb₁ hb₂
    cases of_decide_eq_true hb₁
    cases of_decide_eq_true hb₂
    rfl

theorem countP_mono_right [DecidableEq α] {p : α → Bool} {l l' : List α} (hsub : l ⊆ l') (nodup : l.Nodup) : l.countP p ≤ l'.countP p := by
  induction l generalizing l' with
  | nil => exact Nat.zero_le _
  | cons a l IH =>
    let .cons nodup_head (nodup_tail : l.Nodup) := nodup
    simp only [countP_cons]
    cases hpa : p a <;> simp only [if_pos, if_neg, Nat.add_zero]
    . refine IH (subset_of_cons_subset hsub) nodup_tail
    let l'' := l'.erase a
    have : l ⊆ l'' := fun b h => by
      simp only [List.mem_erase_of_ne (nodup_head b h).symm]
      specialize @hsub b
      simp only [List.mem_cons] at hsub
      exact hsub <| Or.inr h
    specialize IH this nodup_tail
    refine trans (s:=Eq) (Nat.succ_le_succ IH) ?_
    refine Eq.symm <| countP_erase_true ?_ hpa
    exact (cons_subset.mp hsub).1

end List
