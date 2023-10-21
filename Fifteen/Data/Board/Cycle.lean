/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Data.Fin.Basic
import Fifteen.Data.Board.Basic

/-!
# Basic cyclic moves
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false


namespace Board

variable {m n : Nat}

protected def pivot (i : Fin m) (j : Fin n) : Fin ((m+1)*(n+1)) :=
  Fin.rlexProd i.castSucc j.castSucc

theorem pivot_lt_last (i : Fin m) (j : Fin n) : (Board.pivot i j).1 < (m+1)*(n+1)-1 := by
  conv =>
    rhs; change (m+1)*n + m; rw [Nat.add_comm _ m]
    change (Fin.rlexProd (Fin.last m) (Fin.last n)).1
  exact Fin.rlexProd_lt_of_snd _ _ j.2

protected def pathL (i : Fin m) (j : Fin n) : List (Fin ((m+1)*(n+1))) :=
  List.ofFn fun (k : Fin (n-j.1)) =>
    Fin.rlexProd i.castSucc <| (k.natAdd j.1).succ.castLE <| by
      rewrite [Nat.add_sub_cancel' (Nat.le_of_lt j.2)]
      exact .refl

theorem lt_last_of_mem_pathL (i : Fin m) (j : Fin n) (a : Fin ((m+1)*(n+1))) (ha : a ∈ Board.pathL i j) : a.1 < (m+1)*(n+1)-1 := by
  conv at ha => dsimp [Board.pathL]; rw [List.mem_ofFn]
  have ⟨⟨k,hk⟩,ha⟩ := ha; cases ha; dsimp
  conv =>
    change (i.1 + (m+1)*(j.1+k+1)).succ ≤ (m+1)*n+m
    rw [← Nat.succ_add i.1, Nat.add_comm _ m]
  refine Nat.add_le_add i.2 ?_
  refine Nat.mul_le_mul_left (m+1) ?_
  rewrite [Nat.add_comm j.1 k]
  exact Nat.add_lt_of_lt_sub hk

theorem pivot_not_mem_pathL (i : Fin m) (j : Fin n) : Board.pivot i j ∉ Board.pathL i j := by
  dsimp [Board.pathL]; simp only [List.mem_ofFn, not_exists]
  intro k
  refine Fin.ne_of_val_ne (Nat.ne_of_gt ?_)
  apply Fin.rlexProd_lt_of_snd
  show j.1 < j.1 + k + 1
  rewrite [Nat.add_assoc]
  exact j.1.lt_add_of_pos_right k.1.zero_lt_succ

variable (n) in
protected def pathB (i : Fin m) : List (Fin ((m+1)*(n+1))) :=
  List.ofFn fun (k : Fin (m-i.1-1)) =>
    Fin.rlexProd
      ((i.eadd k).succ.castLT <| by
        rewrite [Fin.val_succ, Fin.val_eadd, Nat.add_comm i.1 k.1, Nat.add_assoc]
        apply Nat.add_lt_of_lt_sub
        rewrite [Nat.succ_sub_succ]
        exact trans k.2 ((m-i.1).sub_le 1)
      )
      (Fin.last n)

variable (n) in
theorem lt_last_of_mem_pathB (i : Fin m) (a : Fin ((m+1)*(n+1))) (ha : a ∈ Board.pathB n i) : a.1 < (m+1)*(n+1)-1 := by
  conv at ha => dsimp [Board.pathB]; rw [List.mem_ofFn]
  have ⟨⟨k,hk⟩,ha⟩ := ha; cases ha; simp
  conv => rhs; change (m+1)*n + m; rw [Nat.add_comm _ m]
  refine Nat.add_lt_add_right ?_ _
  rewrite [Nat.add_comm i.1 k, Nat.add_assoc]
  exact Nat.add_lt_of_lt_sub hk

theorem pivot_not_mem_pathB (i : Fin m) (j : Fin n) : Board.pivot i j ∉ Board.pathB n i := by
  dsimp [Board.pathB]; simp only [List.mem_ofFn, not_exists]
  intro k
  refine Fin.ne_of_val_ne (Nat.ne_of_gt ?_)
  exact Fin.rlexProd_lt_of_snd _ _ j.2

variable (m) in
protected def pathR (j : Fin n) : List (Fin ((m+1)*(n+1))) :=
  List.ofFn fun (⟨k,_⟩ : Fin (n-j.1)) =>
    Fin.rlexProd (Fin.last m) <| .mk (n-k-1) <| by
      rewrite [← Nat.sub_add_eq]
      exact trans (n.sub_le (k+1)) n.lt_succ_self

variable (m) in
theorem lt_last_of_mem_pathR (j : Fin n) (a : Fin ((m+1)*(n+1))) (ha : a ∈ Board.pathR m j) : a.1 < (m+1)*(n+1)-1 := by
  conv at ha => dsimp [Board.pathR]; rw [List.mem_ofFn]
  have ⟨⟨k,hk⟩,ha⟩ := ha; cases ha; simp
  conv => rhs; change (m+1)*n + m; rw [Nat.add_comm _ m]
  refine Nat.add_lt_add_left ?_ m
  refine Nat.mul_lt_mul_of_pos_left ?_ m.zero_lt_succ
  rewrite [← Nat.sub_add_eq]
  exact n.sub_lt j.pos k.zero_lt_succ

theorem pivot_not_mem_pathR (i : Fin m) (j : Fin n) : Board.pivot i j ∉ Board.pathR m j := by
  dsimp [Board.pathR, Board.pivot]; simp only [List.mem_ofFn, not_exists]
  intro k
  refine Fin.ne_of_val_ne (Nat.ne_of_gt ?_)
  apply Fin.rlexProd_lt_iff.mpr
  show j.1 < n - k.1 - 1 ∨ _ = _ ∧ i.1 < m
  rewrite [Decidable.or_iff_not_imp_left]
  simp only [Nat.not_lt, Fin.is_lt, and_true]
  intro h
  apply Fin.eq_of_val_eq; dsimp
  apply Nat.le_antisymm ?_ h
  rewrite [← Nat.sub_add_eq]
  apply Nat.le_sub_of_add_le
  show j.1 + k.1 < n
  rewrite [Nat.add_comm j.1 k.1]
  exact Nat.add_lt_of_lt_sub k.2

protected def pathT (i : Fin m) (j : Fin n) : List (Fin ((m+1)*(n+1))) :=
  List.ofFn fun (⟨k,_⟩ : Fin (m-i.1-1)) =>
    Fin.rlexProd
      (.mk (m-k-1) <| by
        rewrite [← Nat.sub_add_eq]
        exact trans (m.sub_le (k+1)) m.lt_succ_self
      )
      j.castSucc

theorem lt_last_of_mem_pathT (i : Fin m) (j : Fin n) (a : Fin ((m+1)*(n+1))) (ha : a ∈ Board.pathT i j) : a.1 < (m+1)*(n+1)-1 := by
  conv at ha => dsimp [Board.pathT]; rw [List.mem_ofFn]
  have ⟨⟨k,hk⟩,ha⟩ := ha; cases ha; simp
  conv => rhs; change (m+1)*n + m; rw [Nat.add_comm _ m]
  apply Nat.add_lt_add
  . rewrite [← Nat.sub_add_eq]
    exact m.sub_lt i.pos k.zero_lt_succ
  . exact Nat.mul_lt_mul_of_pos_left j.2 m.zero_lt_succ

theorem pivot_not_mem_pathT (i : Fin m) (j : Fin n) : Board.pivot i j ∉ Board.pathT i j := by
  dsimp [Board.pathT, Board.pivot]; simp only [List.mem_ofFn, not_exists]
  intro k
  refine Fin.ne_of_val_ne (Nat.ne_of_gt ?_)
  refine Fin.rlexProd_lt_iff.mpr (Or.inr ?_)
  simp only [Fin.castSucc_lt_castSucc_iff, true_and]
  show i < m-k.1-1
  rewrite [← Nat.sub_add_eq]
  apply Nat.lt_sub_of_add_lt
  rewrite [← Nat.add_assoc, Nat.add_comm i.1 k.1, Nat.add_assoc]
  exact Nat.add_lt_of_lt_sub k.2

protected def path (i : Fin m) (j : Fin n) : List (Fin ((m+1)*(n+1))) :=
  Board.pathL i j ++ Board.pathB n i ++ Board.pathR m j ++ Board.pathT i j

theorem lt_last_of_mem_path (i : Fin m) (j : Fin n) (a : Fin ((m+1)*(n+1))) (ha : a ∈ Board.path i j) : a.1 < (m+1)*(n+1)-1 := by
  conv at ha =>
    dsimp [Board.path]
    simp only [List.mem_append, or_assoc]
  rcases ha with hL | hB | hR | hT
  . exact lt_last_of_mem_pathL i j a hL
  . exact lt_last_of_mem_pathB n i a hB
  . exact lt_last_of_mem_pathR m j a hR
  . exact lt_last_of_mem_pathT i j a hT

theorem pivot_not_mem_path (i : Fin m) (j : Fin n) : Board.pivot i j ∉ Board.path i j := by
  dsimp [Board.path]
  simp only [List.mem_append, or_assoc, not_or]
  exact ⟨
    pivot_not_mem_pathL i j,
    pivot_not_mem_pathB i j,
    pivot_not_mem_pathR i j,
    pivot_not_mem_pathT i j
  ⟩

def cycle (i : Fin m) (j : Fin n) : Permutation ((m+1)*(n+1)-1) :=
  Permutation.cyclic <| Fin.restrict (Board.pivot i j) (pivot_lt_last i j) ::
    (Board.path i j).pmap Fin.restrict (lt_last_of_mem_path i j)

theorem sign_cycle (i : Fin m) (j : Fin n) : (cycle i j).sign = false := by
  dsimp [cycle]
  rewrite [Permutation.sign_cyclic_cons]
  . simp only [List.length_pmap, beq_eq_false_iff_ne, ne_eq]
    dsimp [Board.path, Board.pathL, Board.pathB, Board.pathR, Board.pathT]
    simp only [List.length_append, List.length_ofFn]
    rewrite [Nat.add_assoc (n-j.1 + (m-i.1-1)), ← Nat.mul_two, Nat.mul_mod_left]
    decide
  . simp only [List.mem_pmap, not_exists]
    intro a ha hcntr
    cases Fin.restrict_inj _ _ hcntr.2
    exact absurd hcntr.1 <| pivot_not_mem_path i j

def applyCyc (b : Board (m+1) (n+1)) (i : Fin m) (j : Fin n) (k : Int := 1) : Board (m+1) (n+1) :=
  b.apply ((cycle i j)^k) <|
    Permutation.sign_powInt_of_even _ k (sign_cycle i j)

end Board

