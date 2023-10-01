/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Fifteen.Data.Permutation.Basic

/-!
# Random permutation
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u v

/-!
### Preliminaries on random number generators
-/

section Random

variable {gen : Type u} [inst : RandomGen gen]

open private randNatAux in randNat
theorem randNat_range (g : gen) (lo hi : Nat) (h : lo ≤ hi) : lo ≤ (randNat g lo hi).1 ∧ (randNat g lo hi).1 ≤ hi := by
  dsimp [randNat]
  simp only [if_neg (Nat.not_lt_of_le h)]
  generalize (randNatAux (RandomGen.range g).fst ((RandomGen.range g).snd - (RandomGen.range g).fst + 1) ((hi - lo + 1) * 1000) (0, g)).fst = x
  apply And.intro
  . show lo ≤ _
    exact Nat.le_add_right lo _
  . show _ ≤ hi
    conv =>
      rhs; rewrite [← Nat.sub_add_cancel h, Nat.add_comm]
    refine Nat.add_le_add_left ?_ lo
    apply Nat.le_of_lt_succ
    exact x.mod_lt (hi - lo).zero_lt_succ

@[inline]
def randNatWithProof (g : gen) (lo hi : Nat) (h : lo ≤ hi) : {x : Nat // lo ≤ x ∧ x ≤ hi} × gen :=
  match hrg : randNat g lo hi with
  | .mk r g' =>
    have : lo ≤ r ∧ r ≤ hi := by
      rewrite [← (by exact congrArg Prod.fst hrg : (randNat g lo hi).1 = r)]
      exact randNat_range g lo hi h
    ⟨⟨r,this⟩, g'⟩

def IO.randRange (lo hi : Nat) (h : lo ≤ hi): IO {x : Nat // lo ≤ x ∧ x ≤ hi} := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randNatWithProof gen lo hi h
  IO.stdGenRef.set gen
  pure r

end Random


namespace Permutation

/--
Generating a random permutation in the context of `IO` monad.
The algorithm based on the decoding of the Lehmer code.
-/
@[inline]
def random (n : Nat) : IO (Permutation n) :=
  -- The code is stolen from `List.finRange` in `Mathlib`
  let finRange : List (Fin n) :=
    (List.range n).pmap Fin.mk fun _ => List.mem_range.mp
  do
  let mut x : Permutation n := 1
  for i in finRange do
    have : n ≠ 0 := fun h => by cases h; exact i.elim0
    have : i.1 ≤ (n-1) := Nat.le_of_lt_succ <| by
      show i.1 < n.pred.succ
      rewrite [n.succ_pred this]; exact i.2
    let ⟨r,hr⟩ ← IO.randRange i.1 (n-1) this
    x := x.swap i ⟨r, trans hr.2 (n.pred_lt ‹n≠0›)⟩
  return x

end Permutation

