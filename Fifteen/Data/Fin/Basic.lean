/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.Fin.Lemmas

import Fifteen.Data.List.Basic
import Fifteen.Data.Nat.Basic

/-!
# Auxiliary lemmas about `Fin`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

namespace Fin

variable {m n : Nat}

/--
Try to find a term `i : Fin n` satisfying a decidable predicate `p : Fin n → Prop`.
If there is no such a term, then it returns the proof.
-/
def findOrNone {n : Nat} (p : Fin n → Prop) [inst : DecidablePred p] : Subtype p ⊕' (∀ i, ¬ p i) :=
  match n, p, inst with
  | 0, _, _ => PSum.inr fun i => nomatch i
  | n+1, p, _ =>
    match @findOrNone n (p ∘ Fin.castSucc) _ with
    | .inl i => .inl ⟨i.1.castSucc, i.2⟩
    | .inr IH =>
      if hn : p ⟨n,n.lt_succ_self⟩ then
        .inl ⟨⟨n,n.lt_succ_self⟩, hn⟩
      else
        .inr fun i => by
          let ⟨i,hi⟩ := i
          cases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hi) with
          | inl heq => cases heq; exact hn
          | inr hlt => exact IH ⟨i,hlt⟩

theorem restrict_of_not_mem_last {l : List (Fin (n+1))} (h : Fin.last n ∉ l) : ∃ l' : List (Fin n), l = l'.map Fin.castSucc := by
  refine .intro (l.pmap (fun i (hi : i.1 < n) => ⟨i.1,hi⟩) ?_) ?_
  . intro i hi
    cases Nat.eq_or_lt_of_le i.2 with
    | inl heq => cases i; cases heq; exact absurd hi h
    | inr hlt => exact Nat.lt_of_succ_lt_succ hlt
  . apply List.ext_get
    . rw [List.length_map, List.length_pmap]
    . intro i hi _
      rewrite [List.get_map, List.get_pmap]
      rfl

theorem list_length_le_of_nodup {l : List (Fin n)} (nodup : l.Nodup) : l.length ≤ n := by
  induction n with
  | zero =>
    have : l = [] := by cases l; rfl; exact Fin.elim0 ‹_›
    cases this; exact Nat.le.refl
  | succ n IH =>
    if hn : Fin.last n ∈ l then
      let l' := l.erase <| Fin.last n
      have : l'.length = l.length.pred := List.length_erase_of_mem hn
      have : l.length = l'.length + 1 := Eq.symm <| by
        rewrite [this]
        exact Nat.succ_pred_eq_of_pos <| List.length_pos_of_mem hn
      rewrite [this]; refine Nat.succ_le_succ ?_
      have : last n ∉ l' := List.not_mem_erase_of_nodup _ nodup
      let ⟨l'',hl''⟩ := restrict_of_not_mem_last this
      rewrite [hl'', List.length_map]
      refine IH <| List.nodup_of_nodup_map (f:=castSucc) ?_
      rewrite [← hl'']
      exact nodup.erase _
    else
      let ⟨l',hl'⟩ := restrict_of_not_mem_last hn
      cases hl'; rewrite [List.length_map]
      refine trans (IH ?_) (n.le_succ)
      exact List.nodup_of_nodup_map nodup


/-!
### Declarations about `Fin.lexProd`
-/
/--
Fold the product `Fin m × Fin n` into `Fin (m*n)` in the reverse-lexicographical order; i.e. `(i,j) ↦ i + m*j`.
-/
def rlexProd {m n : Nat} (i : Fin m) (j : Fin n) : Fin (m*n) :=
  .mk (i.1 + m*j.1) <| Nat.add_mul_lt_mul i.2 j.2

theorem rlexProd_val_div {m n : Nat} {i : Fin m} {j : Fin n} : (rlexProd i j).1 / m = j.1 := by
  dsimp [rlexProd]
  rewrite [Nat.add_mul_div_left _ _ i.pos, Nat.div_eq_of_lt i.2]
  exact j.1.zero_add

theorem rlexProd_val_mod {m n : Nat} {i : Fin m} {j : Fin n} : (rlexProd i j).1 % m = i.1 := by
  dsimp [rlexProd]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]

theorem rlexProd_inj {m n : Nat} {i₁ i₂ : Fin m} {j₁ j₂ : Fin n} (h : rlexProd i₁ j₁ = rlexProd i₂ j₂) : i₁ = i₂ ∧ j₁ = j₂ := by
  constructor <;> ext
  . rw [← rlexProd_val_mod (i:=i₁) (j:=j₁), ← rlexProd_val_mod (i:=i₂) (j:= j₂), h]
  . rw [← rlexProd_val_div (i:=i₁) (j:=j₁), ← rlexProd_val_div (i:=i₂) (j:= j₂), h]

theorem rlexProd_lt_of_snd {m n : Nat} (i₁ i₂ : Fin m) {j₁ j₂ : Fin n} (h : j₁ < j₂) : rlexProd i₁ j₁ < rlexProd i₂ j₂ := by
  calc i₁.1 + m * j₁.1
    _ < m + m * j₁.1 := Nat.add_lt_add_right i₁.2 _
    _ = m * (j₁.1 + 1) := by rewrite [Nat.add_comm m]; rfl
    _ ≤ m * j₂.1 := Nat.mul_le_mul_left m h
    _ ≤ i₂.1 + m * j₂.1 := Nat.le_add_left ..

theorem rlexProd_lt_iff {m n : Nat} {i₁ i₂ : Fin m} {j₁ j₂ : Fin n} : rlexProd i₁ j₁ < rlexProd i₂ j₂ ↔ (j₁ < j₂ ∨ j₁ = j₂ ∧ i₁ < i₂) := by
  dsimp [rlexProd]; simp only [Fin.lt_def]
  if hj : j₁.1 < j₂.1 then
    simp only [hj, true_or, iff_true]
    exact rlexProd_lt_of_snd i₁ i₂ hj
  else
    simp only [hj, false_or]
    rewrite [Nat.not_lt] at hj
    cases Nat.eq_or_lt_of_le hj with
    | inl heq =>
      cases Fin.eq_of_val_eq heq
      simp only [true_and]
      exact Nat.add_lt_add_iff_right _ i₁.1 i₂.1
    | inr hlt =>
      have : j₁ ≠ j₂ := fun h =>
        Nat.lt_irrefl _ (h ▸ hlt)
      simp only [this, false_and, iff_false, Nat.not_lt]
      apply Nat.le_of_lt
      exact rlexProd_lt_of_snd i₂ i₁ hlt


/-! ### Declarations about `Fin.invOfInj` -/

/--
`OrbitChain f i [i₁, …, iₙ] j` stands for
* `i = f i₁`;
* `iₖ = f iₖ₊₁` for `k = 1, …, n-1`;
* `iₙ = f j`.
-/
inductive OrbitChain (f : Fin n → Fin n) : Fin n → List (Fin n) → Fin n → Prop where
| single (i : Fin n) : OrbitChain f i [] i
| cons {i j : Fin n} {l : List (Fin n)} : f i ∉ (i :: l) → OrbitChain f i l j → OrbitChain f (f i) (i :: l) j

namespace OrbitChain

variable {f : Fin n → Fin n}

private theorem nodup {i j : Fin n} {l : List (Fin n)} (h : OrbitChain f i l j) : (i :: l).Nodup := by
  induction h with
  | single => exact .cons (fun _ h => nomatch h) .nil
  | cons hnotmem _ IH =>
    refine .cons ?_ IH
    intro _ hfa h; cases h
    exact hnotmem hfa

private theorem not_mem {i j : Fin n} {l : List (Fin n)} (h : OrbitChain f i l j) : i ∉ l := by
  cases h with
  | single => exact List.not_mem_nil _
  | cons hnotmem _ => exact hnotmem

private theorem cycle (f_inj : ∀ i j, f i = f j → i = j) {i j : Fin n} {l : List (Fin n)} (h : OrbitChain f i l j) (k : Fin n) (hk : k ∉ l) (hfk : f k ∈ (i :: l)) : f k = j := by
  induction l generalizing i with
  | nil => cases h; exact List.mem_singleton.mp hfk
  | cons k' l IH =>
    cases h with | cons hfk' htail =>
    specialize IH htail (List.not_mem_of_not_mem_cons hk)
    rewrite [List.mem_cons] at hfk
    rewrite [List.mem_cons, not_or] at hk
    cases hfk with
    | inl hfkk' => exact absurd (f_inj _ _ hfkk') hk.1
    | inr h => exact IH h

theorem cons_or_cycle (f_inj : ∀ i j, f i = f j → i = j) {i j : Fin n} {l : List (Fin n)} (h : OrbitChain f i l j) : f i = j ∨ OrbitChain f (f i) (i :: l) j :=
  if hfk : f i ∈ i :: l then
    Or.inl <| cycle f_inj h i h.not_mem hfk
  else
    Or.inr <| .cons hfk h

end OrbitChain

/--
The implementation of `Fin.invOfInjAux`.
The loop does terminates by the following facts:
* every injective map `f : Fin n → Fin n` is bijective;
* the permutation group on `Fin n` is of finite order, and so the inverse `f⁻¹` is of the form `fⁿ` for some `n : Nat`.
-/
unsafe def invOfInjAuxUnsafe (f : Fin n → Fin n) (_ : ∀ (i j : Fin n), f i = f j → i = j) (k : Fin n) : {i : Fin n // f i = k} :=
  let rec go (x : Fin n) : {i : Fin n // f i = k} :=
    let y := f x
    if h : y = k then ⟨x,h⟩ else go y
  go k

/-- `invOfInjAux f h k` compute the inverse image of `k` by a given injective map `f : Fin n → Fin n` together with its proof. -/
@[implemented_by invOfInjAuxUnsafe]
def invOfInjAux (f : Fin n → Fin n) (f_inj : ∀ (i j : Fin n), f i = f j → i = j) (k : Fin n) : {i : Fin n // f i = k} :=
  let rec go (x : Fin n) {l : List (Fin n)} (h : OrbitChain f x l k) : {i : Fin n // f i = k} :=
    if hfx : f x = k then
      ⟨x,hfx⟩
    else
      have : n - (x :: l).length < n - l.length := by
        apply Nat.sub_succ_lt_self
        exact list_length_le_of_nodup h.nodup
      have := (h.cons_or_cycle f_inj).resolve_left hfx
      go (f x) this
  go k (.single k)
termination_by _ => n - l.length

/--
`invOfInj f h k` computes the inverse image of `k` by a given injective map `f`.
See `Fin.invOfInj_right` and `Fin.invOfInj_left` for the proof of the inverseness.
-/
@[inline]
def invOfInj (f : Fin n → Fin n) (f_inj : ∀ i j, f i = f j → i = j) : Fin n → Fin n :=
  fun k => (invOfInjAux f f_inj k).1

theorem invOfInj_right (f : Fin n → Fin n) (f_inj : ∀ i j, f i = f j → i = j) (k: Fin n) : f (invOfInj f f_inj k) = k :=
  (invOfInjAux f f_inj k).2
 
 theorem invOfInj_left (f : Fin n → Fin n) (f_inj : ∀ i j, f i = f j → i = j) (k : Fin n) : invOfInj f f_inj (f k) = k :=
  suffices f (invOfInj f f_inj (f k)) = f k
  from f_inj _ _ this
  invOfInj_right f f_inj (f k)

end Fin
