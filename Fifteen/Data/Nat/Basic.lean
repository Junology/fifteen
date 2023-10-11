/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas
import Std.Data.Fin.Basic

/-!
# Auxiliary declarations about `Nat`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v


namespace Nat

theorem sub_le_self (m n : Nat) : m - n ≤ m :=
  sub_le_of_le_add <| m.le_add_right n

@[elab_as_elim]
theorem decreasing_induction {motive : Nat → Prop} (succ : ∀ n, motive (n+1) → motive n) {m n : Nat} (beg : motive n) (h : m ≤ n) : motive m := by
  induction h with
  | refl => exact beg
  | @step n _ IH => exact IH <| succ _ beg

/--
Dependent analogue of `Nat.fold`.
Given a `Nat`-indexed type family `α : Nat → Sort u`, `Nat.dfold` evaluates `f : (n : Nat) → α n → α (n+1)` on the numbers up to `n` exclusive, in increasing order; i.e.
```
Nat.dfold f 3 init = init |> f 0 |> f 1 |> f 2
```
-/
@[specialize]
def dfold {α : Nat → Sort u} (f : (n : Nat) → α n → α (n+1)) (n : Nat) (init : α 0) : α n :=
  match n with
  | 0 => init
  | n+1 => f n (dfold f n init)

theorem dfold_congr {α β : Nat → Sort u} {f : (n : Nat) → α n → α (n+1)} {g : (n : Nat) → β n → β (n+1)} (hfg : ∀ n a b, HEq a b → HEq (f n a) (g n b)) (n : Nat) {a : α 0} {b : β 0} (hab : HEq a b) : HEq (dfold f n a) (dfold g n b) := by
  have : α = β := funext fun n => by
    suffices ∃ (a : α n) (b : β n), HEq a b
    from let ⟨_,_,hab⟩ := this; type_eq_of_heq hab
    induction n with
    | zero => exact ⟨a,b,hab⟩
    | succ n IH =>
      let ⟨a,b,hab⟩ := IH
      exact ⟨f n a, g n b, hfg n a b hab⟩
  cases this; cases hab
  simp only [heq_iff_eq] at hfg ⊢
  induction n with
  | zero => rfl
  | succ n IH => dsimp [dfold]; exact hfg n _ _ IH

/--
Induction principle on the value computed by `Nat.dfold`.
-/
theorem dfold_induction
  {α : Nat → Sort u} {motive : (n : Nat) → α n → Prop}
  (f : (n : Nat) → α n → α (n+1)) (n : Nat) (init : α 0)
  (zero : motive 0 init)
  (succ : (n : Nat) → (a : α n) → motive n a → motive (n+1) (f n a))
  : motive n (dfold f n init) :=
  match n with
  | 0 => zero
  | n+1 => succ n _ <| dfold_induction f n init zero succ

theorem dfold_hom
  {α : Nat → Sort u} {β : Nat → Sort v}
  (f : (n : Nat) → α n → β n)
  (g₁ : (n : Nat) → α n → α (n+1)) (g₂ : (n : Nat) → β n → β (n+1))
  (n : Nat) (init : α 0)
  (H : ∀ n a, g₂ n (f n a) = f (n+1) (g₁ n a))
  : dfold g₂ n (f 0 init) = f n (dfold g₁ n init) := by
  induction n with
  | zero => rfl
  | succ n IH => dsimp [dfold]; rw [IH, H]

/--
Similar to `Nat.fold`, but this version takes a function of type `Fin n → α → α` instead of `Nat → α → α`.
-/
@[inline]
def fold' {α : Type u} (n : Nat) (f : Fin n → α → α) (init : α) : α :=
  dfold (α := fun i => i ≤ n → α)
    (fun i x hi => f ⟨i,hi⟩ (x <| Nat.le_of_lt hi))
    n (fun _ => init) .refl

theorem fold'_congr {α : Type u} {m n : Nat} (h : m = n) {f : Fin m → α → α} {g : Fin n → α → α} (hf : ∀ i j a, i.1 = j.1 → f i a = g j a) (init : α) : fold' m f init = fold' n g init := by
  cases h
  have : f = g := funext fun i => funext fun a =>
    hf i i a rfl
  cases this
  rfl

@[simp]
theorem fold'_zero {α : Type u} (f : Fin 0 → α → α) (init : α) : fold' 0 f init = init :=
  rfl

theorem fold'_succ {α : Type u} (n : Nat) (f : Fin (n+1) → α → α) (init : α) : fold' (n+1) f init = f (Fin.last n) (fold' n (f ∘ Fin.castSucc) init) := by
  dsimp [fold', dfold]
  apply congrArg
  let mot₁ : Nat → Type u := fun i => i ≤ n+1 → α
  let mot₂ : Nat → Type u := fun i => i ≤ n → α
  suffices ∀ (k : Nat) (hk : k ≤ n), dfold (α:=mot₁) _ k (fun _ => init) (.step hk) = dfold (α:=mot₂) _ k (fun _ => init) hk
  from this n .refl
  intro k hk
  induction k with
  | zero => rfl
  | succ k IH =>
    dsimp [dfold]; apply congrArg
    exact IH (Nat.le_of_succ_le hk)

/--
Induction principle on the computation of `Nat.fold'`.
-/
theorem fold'_induction
  {α : Type u} {motive : Nat → α → Prop}
  (n : Nat) (f : Fin n → α → α) (init : α)
  (zero : motive 0 init)
  (succ : ∀ (i : Nat) (hi : i < n) (a : α), motive i a → motive (i+1) (f ⟨i,hi⟩ a))
  : motive n (fold' n f init) := by
  dsimp [fold', dfold]
  refine dfold_induction (α := fun i => i ≤ n → α) (motive := fun i a => (h : i ≤ n) → motive i (a h)) _ n (fun _ => init) (fun _ => zero) ?_ .refl
  intro i a IH hi
  exact succ i hi _ (IH _)

theorem fold'_hom
  {α : Type u} {β : Type v} (n : Nat)
  (f : α → β) (g₁ : Fin n → α → α) (g₂ : Fin n → β → β) (init : α)
  (H : ∀ i a, g₂ i (f a) = f (g₁ i a))
  : fold' n g₂ (f init) = f (fold' n g₁ init) := by
  dsimp [fold']
  let α' : Nat → Type u := fun i => i ≤ n → α
  let β' : Nat → Type v := fun i => i ≤ n → β
  let f' : (i : Nat) → α' i → β' i :=
    fun i ha hi => f (ha hi)
  let g₁' : (i : Nat) → α' i → α' (i+1) :=
    fun i x hi => g₁ ⟨i,hi⟩ (x <| Nat.le_of_lt hi)
  let g₂' : (i : Nat) → β' i → β' (i+1) :=
    fun i y hi => g₂ ⟨i,hi⟩ (y <| Nat.le_of_lt hi)
  let init' : α' 0 := fun _ => init
  suffices ∀ (k : Nat), dfold g₂' k (f' 0 init') = f' k (dfold g₁' k init') by
    rw [this n]
  intro k
  refine dfold_hom f' g₁' g₂' k init' ?_
  intro i x; dsimp; simp only [H]

@[inline]
def fold'TR {α : Type u} (n : Nat) (f : Fin n → α → α) (init : α) : α :=
  let rec @[specialize] loop : (k : Nat) → k ≤ n → α → α
  | 0  , _, a => a
  | k+1, hk, a =>
    let i : Fin n := .mk (n - (k+1)) <|
      Nat.sub_lt_of_pos_le k.zero_lt_succ hk
    loop k (Nat.le_of_succ_le hk) <| f i a
  loop n .refl init

@[csimp]
theorem fold'_eq_fold'TR : @fold' = @fold'TR := by
  funext α n f init
  suffices ∀ (m n k : Nat) (h : m + n = k) (f : Fin k → α → α), fold'TR.loop k f m (h ▸ m.le_add_right n) (fold' n (fun i => f ⟨i.1, trans i.2 (h ▸ n.le_add_left m)⟩) init) = fold' k f init
  from (this n 0 _ rfl f).symm
  clear n f
  intro m n k h f
  induction m generalizing n k init with
  | zero =>
    rewrite [zero_eq, Nat.zero_add] at h; cases h
    simp only [fold'TR.loop, zero_eq]
  | succ m IH =>
    rewrite [Nat.succ_add] at h; cases h
    dsimp [fold'TR.loop]
    have := fun a => IH a (n+1) (m+n+1) rfl f
    conv at this =>
      ext a; lhs; arg 5; rewrite [fold'_succ]
    rewrite [← this init]
    apply congrArg; apply congrFun; apply congrArg
    apply Fin.eq_of_val_eq
    simp only [Nat.succ_sub_succ_eq_sub, Nat.add_sub_cancel_left]
    rfl

end Nat
