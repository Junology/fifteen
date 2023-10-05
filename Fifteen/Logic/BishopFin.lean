/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Tactic.Basic

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

variable {α : Type u} {β : Type v} [BishopFin α] [BishopFin β]

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

theorem _root_.List.Nodup.length_le_card {l : List α} (nodup : l.Nodup) : l.length ≤ card α :=
  nodup.length_le_of_subset <| subset_elems l

theorem card_le_card_of_inj (f : α → β) (f_inj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) : card α ≤ card β := by
  dsimp only [card]
  conv =>
    lhs; equals ((elems α).map f).length => rw [List.length_map]
  refine List.Nodup.length_le_of_subset ?_ ?_
  . exact nodup_elems.map f f_inj
  . exact subset_elems _

theorem card_ge_card_of_surj (f : α → β) (f_surj : ∀ b, ∃ a, f a = b) : card α ≥ card β := by
  dsimp only [card]
  conv =>
    lhs; equals ((elems α).map f).length => rw [List.length_map]
  refine nodup_elems.length_le_of_subset ?_
  intro b _
  simp only [List.mem_map, mem_elems, true_and]
  exact f_surj b

theorem card_eq_card_of_bij [BishopFin β] (f : α → β) (f_surj : ∀ b, ∃ a, f a = b) (f_inj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) : card α = card β := by
  refine Nat.le_antisymm ?_ ?_
  . exact card_le_card_of_inj f f_inj
  . exact card_ge_card_of_surj f f_surj

theorem card_eq_card_of_inv (f : α → β) (g : β → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) : card α = card β := by
  refine Nat.le_antisymm ?_ ?_
  . show card α ≤ card β
    refine card_le_card_of_inj f ?_
    intros a₁ a₂ hfa
    rw [← hgf a₁, ← hgf a₂, hfa]
  . show card β ≤ card α
    refine card_le_card_of_inj g ?_
    intro b₁ b₂ hgb
    rw [← hfg b₁, ← hfg b₂, hgb]

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

theorem card_subset_le_card {α : Type u} {p : α → Prop} [BishopFin α] [DecidablePred p] : card {a // p a} ≤ card α := by
  apply card_le_card_of_inj Subtype.val
  intro _ _; exact Subtype.eq


/-! ### Counting elements -/

section Count

variable {α : Type u} {β : Type v} [BishopFin α] [BishopFin β]

/-- Counting the number of elements in a Bishop finite type `α` satisfying a decidable predicate `p : α → Prop`. -/
@[inline]
def count (p : α → Prop) [DecidablePred p] : Nat :=
  BishopFin.elems α |>.countP fun a => decide (p a)

@[inherit_doc BishopFin.count] syntax "#| " withoutPosition(ident (" : " term)? " // " term) " |" : term

scoped macro_rules
| `(#| $x : $type // $p |) => ``(BishopFin.count (fun ($x:ident : $type) => $p))
| `(#| $x // $p |)         => ``(BishopFin.count (fun ($x:ident : _) => $p))


variable {p q : α → Prop} [DecidablePred p] [DecidablePred q]

theorem count_eq_card : count p = card {a // p a} := by
  dsimp [count]; rewrite [List.countP_eq_length_filter]
  conv => rhs; change subtype (p:=p) |>.elems' |>.length
  dsimp [elems']; simp only [List.length_pmap]

theorem count_le : count p ≤ card α :=
  List.countP_le_length _

@[simp]
theorem count_true : count (fun (_ : α) => True) = card α := by
  dsimp [count]; rewrite [List.countP_true]; rfl

@[simp]
theorem count_false : count (fun (_ : α) => False) = 0 :=
  List.countP_false

theorem count_mono_left (h : ∀ a, p a → q a) : count p ≤ count q :=
  List.countP_mono_left fun a _ ha =>
    have : q a := h a (of_decide_eq_true ha)
    decide_eq_true this

theorem count_congr (h : ∀ a, p a ↔ q a) : count p = count q :=
  Nat.le_antisymm
    (count_mono_left fun a => (h a).1)
    (count_mono_left fun a => (h a).2)

theorem count_eq_count_sub (h : ∀ a, p a → q a) : count p = count (p ∘ Subtype.val (p:=q)) := by
  iterate rewrite [count_eq_card]
  refine card_eq_card_of_inv ?f ?g ?hgf ?hfg
  . exact fun x => ⟨⟨x.1, h x.1 x.2⟩, x.2⟩
  . exact fun y => ⟨y.1.1, y.2⟩
  all_goals simp

@[simp]
theorem count_le_one_of_unique (p_unique : ∀ a b, p a → p b → a = b) : count p ≤ 1 := by
  dsimp [count]
  refine List.countP_le_one_of_unique_nodup ?_ nodup_elems
  simp only [decide_eq_true_eq]
  exact p_unique

variable (p) in
theorem card_eq_count_add_count_not : card α = count p + count (fun a => ¬ p a) := by
  dsimp [card]
  rewrite [(elems α).length_eq_countP_add_countP p]
  apply congrArg (count p + ·)
  simp only [decide_eq_true_eq]
  rfl

theorem count_or_le_add : count (fun a => p a ∨ q a) ≤ count p + count q := by
  dsimp [count]; simp only [decide_or, List.countP_or_le_add]

theorem count_disjoint_or (h : ∀ a, ¬(p a ∧ q a)) : count (fun a => p a ∨ q a) = count p + count q := by
  dsimp [count]; simp only [decide_or]
  apply List.countP_disjoint
  simp only [← decide_and, decide_eq_false_iff_not]
  exact h

variable (q) in
theorem count_split : count p = count (fun a => p a ∧ q a) + count (fun a => p a ∧ ¬ q a) := by
  conv =>
    lhs
    rewrite [count_eq_card, card_eq_count_add_count_not (q ∘ Subtype.val)]
  refine congr (congrArg _ ?_) ?_
  all_goals (
    simp only [count_eq_card]
    apply card_eq_card_of_bij fun x => ⟨x.1.1, x.1.2, x.2⟩
    . intro y; exact ⟨⟨⟨y.1,y.2.1⟩,y.2.2⟩,rfl⟩
    . intro x₁ x₂
      simp only [Subtype.mk.injEq]
      exact Subtype.eq ∘ Subtype.eq
  )

theorem count_image_le_card [DecidableEq β] (f : α → β) : count (fun b => ∃ a, f a = b) ≤ card α := by
  have := (elems α).countP_image_le_length nodup_elems (f := f)
  simp only [mem_elems, true_and] at this
  exact this

theorem count_image_le_count [DecidableEq β] (f : α → β) : count (fun b => ∃ a, p a ∧ f a = b) ≤ count p := by
  conv => rhs; rewrite [count_eq_card]
  refine trans (r:=Eq) ?_ (count_image_le_card (f ∘ Subtype.val))
  apply count_congr
  intro b; constructor
  . intro h; let ⟨a,hpa,hfa⟩ := h
    exact ⟨⟨a,hpa⟩, hfa⟩
  . intro h; let ⟨⟨a,hpa⟩,hfa⟩ := h
    exact ⟨a,hpa,hfa⟩

theorem count_le_count_invimage [DecidableEq α] (f : β → α) (hf : ∀ a, p a → ∃ b, f b = a) : count p ≤ count (p ∘ f) := by
  rewrite [count_eq_count_sub hf]
  let f' : β → {a // ∃ b, f b = a} := fun b => ⟨f b, b, rfl⟩
  have : f = Subtype.val ∘ f' := funext fun _ => rfl
  rewrite [this]
  dsimp [count]
  conv =>
    rhs; equals ((elems β).map f').countP (fun a => decide (p a.val)) =>
      rewrite [List.countP_map]; rfl
  refine List.countP_mono_right ?_ nodup_elems
  intro x _; simp only [List.mem_map]
  let ⟨a,b,ha⟩ := x
  exists b; apply And.intro (mem_elems b)
  exact Subtype.eq ha

/--
:::note info
In contrast to `BishopFin.count_le_count_invimage`, this function does not require `DecidableEq α`.
:::
-/
theorem count_le_count_invimage_of_surj (f : β → α) (f_surj : ∀ a, ∃ b, f b = a) : count p ≤ count (p ∘ f) := by
  iterate rewrite [count_eq_card]
  refine card_ge_card_of_surj ?f ?f_surj
  . exact fun y => ⟨f y.1, y.2⟩
  . intro x
    let ⟨a,ha⟩ := x
    let ⟨b,hb⟩ := f_surj a
    exists ⟨b, by dsimp; exact hb ▸ ha⟩
    exact Subtype.eq hb

theorem count_invimage_le_count_of_inj (f : β → α) (f_inj : ∀ b₁ b₂, f b₁ = f b₂ → b₁ = b₂) : count (p ∘ f) ≤ count p := by
  iterate rewrite [count_eq_card]
  refine card_le_card_of_inj ?f ?f_inj
  . exact fun y => ⟨f y.1, y.2⟩
  . intro y₁ y₂ h
    apply Subtype.eq; apply f_inj
    exact congrArg Subtype.val h

theorem count_eq_count_invimage_of_bij (f : β → α) (f_surj : ∀ a, ∃ b, f b = a)  (f_inj : ∀ b₁ b₂, f b₁ = f b₂ → b₁ = b₂) : count p = count (p ∘ f) := by
  refine Nat.le_antisymm ?_ ?_
  . exact count_le_count_invimage_of_surj f f_surj
  . exact count_invimage_le_count_of_inj f f_inj

theorem count_eq_count_invimage_of_inv (f : β → α) (g : α → β) (hgf : ∀ b, g (f b) = b) (hfg : ∀ a, f (g a) = a) : count p = count (p ∘ f) := by
  refine count_eq_count_invimage_of_bij f ?_ ?_
  . exact fun a => ⟨g a, hfg a⟩
  . intro b₁ b₂ hb
    rw [← hgf b₁, ← hgf b₂, hb]

end Count


end BishopFin

