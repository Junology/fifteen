/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Nat.Lemmas

/-!
# Auxiliary declarations about `Nat`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v


namespace Nat

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

end Nat
