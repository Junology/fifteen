/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Data.List.Basic

/-!
# Bishop finiteness

A type `α` is said to be ***Bishop finite*** (or just ***finite*** if there is no danger of confusion with other types of finiteness) if there is a bijection between `α` and `Fin n`.
This is equivalent to saying that `α` admits a list `l : α` satisfying

* `∀ a : α, a ∈ l`
* `l.Nodup`

## Remark

In contrast to `Fintype` class in `Mathlib`, we use `List α` instead of (any counterpart of) `Finset α`.

-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v

class BishopFin (α : Type u) : Type u where
  elems' : List α
  nodup_elems' : elems'.Nodup
  mem_elems' : ∀ a, a ∈ elems'

namespace BishopFin

section Basic

/-! ### Basic declarations -/

variable {α : Type u} [BishopFin α]

variable (α) in
/--
Get an exhaustive list of elements of type `α` without duplication.
See also `BishopFin.nodup_elems` and `BishopFin.mem_elems`.
-/
@[inline]
abbrev elems : List α := elems'

theorem nodup_elems : (elems α).Nodup :=
  nodup_elems'

theorem mem_elems : ∀ a, a ∈ elems α :=
  mem_elems'

theorem subset_elems (l : List α) : l ⊆ elems α :=
  fun a _ => mem_elems a

variable (α) in
/-- The cardinality of a Bishop finite type. -/
@[inline]
def card : Nat :=
  (elems α).length

theorem _root_.List.Nodup.length_le_card [DecidableEq α] {l : List α} (nodup : l.Nodup) : l.length ≤ card α :=
  nodup.length_le_of_subset <| subset_elems l

instance (priority:=0) decidableEx (p : α → Prop) [DecidablePred p] : Decidable (∃ a, p a) :=
  if hp : ∃ a, (a ∈ elems α ∧ p a) then
    .isTrue <| by simp only [mem_elems, true_and] at hp; exact hp
  else
    .isFalse <| by simp only [mem_elems, true_and] at hp; exact hp

instance (priority:=0) decidableAll (p : α → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  if hp : ∀ a, a ∈ elems α → p a then
    .isTrue fun a => hp a <| mem_elems a
  else
    .isFalse <| by simp only [mem_elems, true_implies] at hp; exact hp

end Basic


/-! ### Instances -/

instance fin {n : Nat} : BishopFin (Fin n) where
  elems' :=
    List.pmap Fin.mk (List.range n) fun _ => List.mem_range.mp
  nodup_elems' := by
    apply List.Nodup.pmap
    . exact List.nodup_range n
    . intro i j hi hj; exact Fin.val_eq_of_eq
  mem_elems' i := by
    apply List.mem_pmap.mpr
    simp only [List.mem_range]
    exact ⟨i.1, i.2, i.2, rfl⟩

instance prod {α : Type u} {β : Type v} [BishopFin α] [BishopFin β] : BishopFin (α × β) where
  elems' := (elems α).product (elems β)
  nodup_elems' := nodup_elems.product nodup_elems
  mem_elems' := fun
    | .mk a b => List.pair_mem_product.mpr ⟨mem_elems a, mem_elems b⟩

instance subtype {α : Type u} {p : α → Prop} [BishopFin α] [DecidablePred p] : BishopFin (Subtype p) where
  elems' :=
    (elems α).filter (fun a => decide (p a)) |>.pmap Subtype.mk fun a ha => by
      simp only [List.mem_filter, decide_eq_true_eq] at ha
      exact ha.2
  nodup_elems' := by
    refine List.Nodup.pmap ?_ _ _ ?_
    . exact (nodup_elems (α:=α)).filter _
    . intros; exact congrArg Subtype.val ‹_›
  mem_elems' a := by
    simp only [List.mem_pmap, List.mem_filter, mem_elems, true_and, decide_eq_true_eq]
    exact ⟨a.1, a.2, a.2, rfl⟩


/-! ### Counting elements -/

section Count

variable {α : Type u} [BishopFin α]

/-- Counting the number of elements in a Bishop finite type `α` satisfying a decidable predicate `p : α → Prop`. -/
@[inline]
def count (p : α → Prop) [DecidablePred p] : Nat :=
  BishopFin.elems α |>.countP fun i => decide (p i)

theorem count_eq_card {p : α → Prop} [DecidablePred p] : count p = card {a // p a} := by
  dsimp [count]; rewrite [List.countP_eq_length_filter]
  conv => rhs; change subtype (p:=p) |>.elems' |>.length
  dsimp [elems']; simp only [List.length_pmap]

theorem count_le {p : α → Prop} [DecidablePred p] : count p ≤ card α :=
  List.countP_le_length _

@[simp]
theorem count_true : count (fun (_ : α) => True) = card α := by
  dsimp [count]; rewrite [List.countP_true]; rfl

@[simp]
theorem count_false : count (fun (_ : α) => False) = 0 :=
  List.countP_false

theorem count_mono_left {p q : α → Prop} [DecidablePred p] [DecidablePred q] (h : ∀ a, p a → q a) : count p ≤ count q :=
  List.countP_mono_left fun a _ ha =>
    have : q a := h a (of_decide_eq_true ha)
    decide_eq_true this

@[simp]
theorem count_le_one_of_unique (p : α → Prop) [DecidablePred p] (p_unique : ∀ a b, p a → p b → a = b) : count p ≤ 1 := by
  dsimp [count]
  refine List.countP_le_one_of_unique_nodup ?_ nodup_elems
  simp only [decide_eq_true_eq]
  exact p_unique

theorem count_image_le {β : Type v} [DecidableEq β] [BishopFin β] (f : α → β) : count (fun b => ∃ a, f a = b) ≤ card α := by
  have := (elems α).countP_image_le_length nodup_elems (f := f)
  simp only [mem_elems, true_and] at this
  exact this

end Count


end BishopFin

