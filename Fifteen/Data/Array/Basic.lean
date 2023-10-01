/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.List.Lemmas
import Std.Data.Array.Lemmas

import Fifteen.Data.List.Basic

/-!
# Auxiliary lemmas about `Array`
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u

namespace Array

variable {α : Type u}

/-- The counterpart of `List.Nodup` in `Std` -/
def Nodup (as : Array α) : Prop :=
  as.data.Nodup

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

end Array

