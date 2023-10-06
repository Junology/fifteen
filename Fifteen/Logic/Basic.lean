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

theorem Bool.bne_comm (a b : Bool) : (a != b) = (b != a) := by
  cases a <;> cases b <;> decide

theorem Bool.bne_assoc (a b c : Bool) : ((a != b) != c) = (a != (b != c)) := by
  cases a <;> cases b <;> cases c <;> decide

@[simp]
theorem Bool.bne_self (a : Bool) : (a != a) = false := by
  cases a <;> decide

@[simp]
theorem Bool.bne_false (a : Bool) : (a != false) = a := by
  cases a <;> decide

@[simp]
theorem Bool.false_bne (a : Bool) : (false != a) = a := by
  cases a <;> decide

theorem Bool.bne_eq_false (a b : Bool) : (a != b) = false ↔ a = b := by
  cases a <;> cases b <;> decide

