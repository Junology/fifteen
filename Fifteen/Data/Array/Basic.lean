/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas

import Fifteen.Data.Nat.Basic
import Fifteen.Data.List.Basic

/-!
# Auxiliary lemmas about `Array`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v w

namespace Array

variable {α : Type u}

/--
:::note warn
This theorem depends on `Classical.choice` since `Array.append_data` does.
:::
-/
theorem size_append (as bs : Array α) : (as ++ bs).size = as.size + bs.size := by
  dsimp [size]; rw [append_data, List.length_append]

theorem size_shrink_loop (as : Array α) {k : Nat} (h : k ≤ as.size) : (shrink.loop k as).size = as.size - k := by
  induction k generalizing as with
  | zero => rfl
  | succ k IH =>
    dsimp [shrink.loop]
    have : as.size = as.pop.size + 1 := by
      rw [as.size_pop, Nat.sub_add_cancel (trans (r:=LE.le (α:=Nat)) (s:=LT.lt (α:=Nat)) k.zero_le h)]
    rewrite [this] at h ⊢
    rewrite [IH as.pop (Nat.le_of_succ_le_succ h)]
    simp only [Nat.succ_sub_succ_eq_sub]

theorem size_shrink (as : Array α) {n : Nat} (h : n ≤ as.size) : (as.shrink n).size = n := by
  refine Eq.trans (size_shrink_loop as ?_) ?_
  . exact as.size.sub_le_self n
  . exact Nat.sub_sub_self h

theorem any_eq_any_data (as : Array α) (p : α → Bool) : as.any p = as.data.any p := by
  dsimp [any, anyM]; simp
  conv => rhs; change (as.data.drop 0).any p
  refine Nat.decreasing_induction (m:=0) (n:=as.size) ?_ ?_ as.size.zero_le
  . intro j IH
    unfold anyM.loop; dsimp
    if hlt : j < as.size then
      rewrite [dif_pos hlt, ← List.get_drop_eq_drop _ _ hlt, List.any_cons, List.getElem_eq_get, ← Array.getElem_eq_data_get]
      if hpj : p (as[j]'hlt) = true then
        rewrite [if_pos hpj, hpj, Bool.true_or]
        rfl
      else
        rw [if_neg hpj, IH, Bool.eq_false_iff.mpr hpj, Bool.false_or]
    else
      rewrite [dif_neg hlt, List.drop_eq_nil_of_le (Nat.le_of_not_lt hlt)]
      rfl
  . unfold anyM.loop; dsimp
    rewrite [dif_neg (Nat.lt_irrefl _), List.drop_eq_nil_of_le .refl]
    rfl

theorem swap_comm (as : Array α) (i j : Fin as.size) : as.swap i j = as.swap j i := by
  apply Array.ext'; simp only [Array.data_swap]
  if h : i.1 = j.1 then
    cases Fin.eq_of_val_eq h; rfl
  else
    rw [List.set_comm _ _ _ h]


/-! ### Declarations about `Array.pam` -/

section PMap

variable {β : Type v} {p : α → Prop}
/--
The runtime implementation of `Array.pmapM`.
This function is just an alias of `Array.mapMUnsafe`.
-/
@[inline]
unsafe def pmapMUnsafe {m : Type v → Type w} [Monad m] (f : (a : α) → p a → m β) (as : Array α) (_ : ∀ (i : Nat) (hi : i < as.size), p as[i]) : m (Array β) :=
  as.mapMUnsafe fun a => f a lcProof

/-- The `Array`-counterpart of `List.pmap` in a monad context. -/
@[implemented_by pmapMUnsafe]
def pmapM {m : Type v → Type w} [Monad m] (f : (a : α) → p a → m β) (as : Array α) (h : ∀ (i : Nat) (hi : i < as.size), p as[i]) : m (Array β) :=
  let rec map (i : Nat) (r : Array β) : m (Array β) := do
    if hlt : i < as.size then
      map (i+1) (r.push (← f as[i] (h i hlt)))
    else
      pure r
  map 0 (Array.mkEmpty as.size)
termination_by map => as.size - i

/-- The `Array`-counterpart of `List.pmap`. -/
@[inline]
def pmap (f : (a : α) → p a → β) (as : Array α) (h : ∀ (i : Nat) (hi : i < as.size), p as[i]) : Array β :=
  pmapM (m:=Id) f as h

theorem pmap_eq_nat_fold'_push (f : (a : α) → p a → β) (as : Array α) (h : ∀ (i : Nat) (hi : i < as.size), p as[i]) : as.pmap f h = Nat.fold' as.size (fun i x => x.push <| f as[i.1] (h i.1 i.2)) #[] := by
  rewrite [Nat.fold'_eq_fold'TR]
  dsimp [pmap, pmapM, Nat.fold'TR]
  suffices ∀ (k : Nat) (hk : k ≤ as.size) (bs : Array β), pmapM.map (m:=Id) f as h (as.size - k) bs = Nat.fold'TR.loop as.size _ k hk bs
  from Eq.trans (as.size.sub_self ▸ rfl) (this as.size .refl #[])
  intro k hk bs
  induction k generalizing bs with
  | zero =>
    simp only [Nat.zero_eq, Nat.sub_zero]
    unfold pmapM.map
    exact dif_neg <| Nat.lt_irrefl as.size
  | succ k IH =>
    unfold pmapM.map
    rewrite [dif_pos (trans (as.size.sub_succ_lt_self _ hk) (as.size.sub_le k))]
    dsimp [Nat.fold'TR.loop]
    rw [← IH (Nat.le_of_succ_le hk) _]
    apply congrFun; apply congrArg
    rewrite [← Nat.sub_add_comm hk]
    exact Nat.succ_sub_succ_eq_sub as.size k

theorem size_pmap (f : (a : α) → p a → β) (as : Array α) (h : ∀ (i : Nat) (hi : i < as.size), p as[i]) : (as.pmap f h).size = as.size := by
  rewrite [pmap_eq_nat_fold'_push]
  refine Nat.fold'_induction (motive := fun k (x : Array β) => x.size = k) as.size _ #[] rfl ?_
  intro i hi x hx
  simp only [size_push, hx]

end PMap


/-! ### Lemmas about `GetElem.getElem` -/

theorem getElem_pop (as : Array α) (i : Nat) (hi : i < as.pop.size) : as.pop[i] = as[i]'(trans (r:=LT.lt (α:=Nat)) (s:=LE.le) hi (as.size_pop ▸ as.size.sub_le_self 1)) := by
  dsimp [pop]
  simp only [getElem_eq_data_get, List.dropLast_eq_take, List.get_take]
  exact as.data.get_take _ i

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

theorem getElem_shrink (as : Array α) {n : Nat} (h : n ≤ as.size) (i : Nat) (hi : i < (as.shrink n).size) : (as.shrink n)[i] = as[i]'(trans (r:=LT.lt (α:=Nat)) (as.size_shrink h ▸ hi) h) := by
  dsimp [shrink] at hi ⊢
  revert i
  suffices ∀ (i k : Nat) (hk : k ≤ as.size) (hi : i < as.size - k), (shrink.loop k as)[i]'(as.size_shrink_loop hk ▸ hi) = as[i]'(trans (r:=LT.lt (α:=Nat)) hi (as.size.sub_le_self k))
  from fun i hi =>
    this i (as.size - n) (as.size.sub_le_self n) (by rw [Nat.sub_sub_self h]; exact trans (r:=LT.lt (α:=Nat)) (s:=Eq) hi (as.size_shrink h))
  clear h n
  intro i k hk hi
  induction k generalizing as with
  | zero => rfl
  | succ k IH =>
    dsimp [shrink.loop]
    specialize IH as.pop (as.size_pop ▸ Nat.le_sub_of_add_le hk) (by rewrite [as.size_pop, Nat.sub_sub, Nat.add_comm]; exact hi)
    rewrite [IH]
    exact as.getElem_pop i _

/--
:::note warn
This lemma depends on `Classical.choice` because of `Array.get_push_eq` and `Array.get_push_lt`.
:::
-/
theorem getElem_pmap {β : Type v} {p : α → Prop} (f : (a : α) → p a → β) (as : Array α) (h : ∀ (i : Nat) (hi : i < as.size), p as[i]) (i : Nat) {hi : i < (as.pmap f h).size} : (as.pmap f h)[i] = f (as[i]'(as.size_pmap f h ▸ hi)) (h i <| as.size_pmap f h ▸ hi) := by
  simp only [pmap_eq_nat_fold'_push]
  refine Nat.fold'_induction
    (motive := fun (k : Nat) (bs : Array β) => ∀ (j : Nat) (hjk : j < k) (hk : k ≤ as.size) (hbsk : bs.size = k), bs[j]'(hbsk ▸ hjk) = f (as[j]'(trans (r:=LT.lt (α:=Nat)) hjk hk)) (h j (trans (r:=LT.lt (α:=Nat)) hjk hk)))
    as.size _ #[] ?_ ?_ i (as.size_pmap f h ▸ hi) .refl ((as.pmap_eq_nat_fold'_push f h) ▸ as.size_pmap f h)
  . intro k hk; cases hk
  . intro k hk bs IH j hj _ hbsk
    simp only [Array.size_push] at hbsk ⊢
    cases hbsk
    cases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hj) with
    | inl heq =>
      cases heq; exact get_push_eq ..
    | inr hlt =>
      rewrite [bs.get_push_lt _ j hlt]
      exact IH j hlt (Nat.le_of_lt hk) rfl


/-! ### Membership relation -/

section Membership

variable [DecidableEq α]

theorem mem_iff_mem_data {a : α} {as : Array α} : a ∈ as ↔ a ∈ as.data := by
  show as.any (fun b => a = b) = true ↔ a ∈ as.data
  rewrite [any_eq_any_data]
  simp only [List.any_eq_true, List.mem_iff_get]
  constructor
  . intro h
    let ⟨_, ⟨i,hi⟩, h⟩ := h
    cases of_decide_eq_true h
    exact ⟨i,hi⟩
  . intro h; exists a; simp; exact h

theorem mem_push {a b : α} {as : Array α} : a ∈ as.push b ↔ a ∈ as ∨ a = b := by
  rw [mem_iff_mem_data, push_data, List.mem_append, mem_iff_mem_data, List.mem_singleton]

end Membership


/-! ### Declaration about `Array.Nodup` -/

/-- The counterpart of `List.Nodup` in `Std` -/
def Nodup (as : Array α) : Prop :=
  as.data.Nodup

instance {α : Type u} [DecidableEq α] (as : Array α): Decidable as.Nodup :=
  inferInstanceAs (Decidable as.data.Nodup)

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

theorem nodup_push [DecidableEq α] {as : Array α} {a : α} : (as.push a).Nodup ↔ as.Nodup ∧ a ∉ as := by
  show (as.push a).data.Nodup ↔ as.Nodup ∧ a ∉ as
  rewrite [Array.push_data]
  apply Iff.trans List.pairwise_append
  show as.Nodup ∧ [a].Nodup ∧ _ ↔ _
  simp only [List.nodup_singleton a, true_and, ← mem_iff_mem_data, List.mem_singleton, forall_eq]
  apply and_congr_right'
  constructor
  . intro h ha; exact h a ha rfl
  . intro ha b hb heq; cases heq; exact ha hb

theorem Nodup.push [DecidableEq α] {as : Array α} (has : as.Nodup) {a : α} (ha : a ∉ as) : (as.push a).Nodup :=
  nodup_push.mpr ⟨has,ha⟩

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

