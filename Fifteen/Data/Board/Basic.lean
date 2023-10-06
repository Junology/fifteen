/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Data.Permutation.Basic
import Fifteen.Data.Permutation.Sign
import Fifteen.Data.Permutation.Random

/-!
# Boards of `(m*n-1)`-puzzles
-/

structure Board (m n : Nat) where
  val : Permutation (m*n - 1)
  even : val.sign = false
  deriving DecidableEq, Repr

namespace Board

variable {m n : Nat}

variable (m n) in
/-- The "solved" board. -/
@[inline]
def solved : Board m n :=
  .mk 1 Permutation.sign_one

variable (m n) in
/--
Generate a random board.
Notice that the boards of the `(m*n-1)`-puzzle correspond in one-to-one to an alternating permutations.
-/
@[inline]
def random : IO (Board m n) := do
  if h : 1 < m * n - 1 then
    let x ← Permutation.randomIO (m*n-1)
    if hx : x.sign = true then
      return .mk (x.swap ⟨0,trans Nat.zero_lt_one h⟩ ⟨1,h⟩) <| by
        rw [Permutation.sign_swap, hx, Bool.not_true]
        intro h; cases h
    else
      return .mk x <| Bool.of_not_eq_true hx
  else
    return solved m n

/--
Apply an even permutation to the board.
-/
@[inline]
def apply (b : Board m n) (x : Permutation (m*n-1)) (h : x.sign = false) : Board m n :=
  .mk (x * b.val) <| by
    simp only [Permutation.sign_mul, h, b.even]

end Board

