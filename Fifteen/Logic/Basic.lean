/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Auxiliary lemmas about propositions and `Bool`
-/

theorem decide_or {p q : Prop} [Decidable p] [Decidable q] : decide (p ∨ q) = (decide p || decide q) := by
  apply dite p <;> apply dite q <;> intro hp hq <;> simp [hp, hq]

theorem decide_and {p q : Prop} [Decidable p] [Decidable q] : decide (p ∧ q) = (decide p && decide q) := by
  apply dite p <;> apply dite q <;> intro hp hq <;> simp [hp, hq]


