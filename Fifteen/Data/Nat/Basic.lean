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

end Nat
