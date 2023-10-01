/-
Copyright (c) 2023 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.Array.Lemmas

import Fifteen.Data.List.Basic
import Fifteen.Data.Array.Basic
import Fifteen.Data.Fin.Basic


/-!
# Permutations on `Fin n`

A ***permutation*** on a finite set is a bijection on it into itself.
In particular, in this file, we discuss permutations on `Fin n` for `n : Nat`.
In this case, each permutation `f` on `Fin n` is represented by the array of its images `#[f 0, f 1, …, f (n-1)]`.
Conversely, an array `x : Array (Fin n)` represents a permutation provided `x.size = n` and `x.Nodup`.
This is why we define `Permutation n` as a structure type consisting of `Array (Fin n)` together with these properties.

We show that `Permutation n` forms a group and provide several special permutations.

## Main declarations

* `Permutation`: the structure type representig permutations on `Fin n`.
* `Permutation.id` / `Permutation.comp` / `Permutation.inv`: the group structure on `Permutation n`.
-/

set_option autoImplicit false

universe u v

/-! ### Main structure -/

/--
`Permutation n` is the type for permutations on the set {0,1,…,n-1}.
Each permutation is represented by an array `x : Array (Fin n)` so that it maps as `i ↦ x[i]`.
Hence, it requires `x.size = n` and `x.Nodup` to ensure the mapping is bijective.
-/
structure Permutation (n : Nat) where
  val : Array (Fin n)
  size_eq : val.size = n
  nodup : val.Nodup
  deriving DecidableEq, Repr


namespace Permutation

variable {n : Nat}


/-! ### Basic declarations -/

protected theorem eq (x y : Permutation n) (h : x.val = y.val) : x = y :=
  match x, y, h with
  | .mk _ _ _, .mk _ _ _, rfl => rfl

instance : GetElem (Permutation n) Nat (Fin n) (fun _ i => i < n) where
  getElem x i hi := x.val[i]'(x.size_eq.symm ▸ hi)

theorem ext (x y : Permutation n) (h : ∀ (i : Nat) (hi : i < n), x[i] = y[i]) : x = y :=
  Permutation.eq x y <|
    Array.ext x.val y.val (x.size_eq.trans y.size_eq.symm) fun i hi _ =>
      h i (x.size_eq ▸ hi)

theorem get_inj (x : Permutation n) (i j : Nat) {hi : i < n} {hj : j < n} (h : x[i] = x[j]) : i = j :=
  x.nodup.get_inj i j <| h

theorem get_inj' (x : Permutation n) (i j : Fin n) (h : x[i.1] = x[j.1]) : i = j :=
  Fin.eq_of_val_eq <| x.get_inj _ _ h

/-- `Permutation.toFun x` is the mapping `Fin n → Fin n` corresponding to the given permutation `x : Permutation n`. -/
@[inline]
def toFun (x : Permutation n) (i : Fin n) : Fin n :=
  x[i.1]

/-- Every map corrsponding to `x : Permutation n` is injective. -/
theorem toFun_inj (x : Permutation n) (i j : Fin n) : x.toFun i = x.toFun j → i = j :=
  x.get_inj' i j

/-- Two permutations `x y : Permutation n` equal to each other provided their corresponding map do; i.e. `x.toFun = y.toFun`. -/
theorem eq_of_toFun_eq (x y : Permutation n) (h : x.toFun = y.toFun) : x = y :=
  ext x y fun i hi => congrFun h ⟨i,hi⟩

/--
Define a permutation from an injective map `Fin n → Fin n`.

:::note warn
The function currently depends on `Classical.choice` since `Array.nodup_ofFn` does
:::
-/
@[inline]
def ofFn (f : Fin n → Fin n) (f_inj : ∀ i j, f i = f j → i = j) : Permutation n where
  val := Array.ofFn f
  size_eq := Array.size_ofFn f
  nodup := Array.nodup_ofFn f f_inj

/--
The image of the permutation of the form `Permutation.ofFn f h` agrees with that of `f`.

:::note warn
The function currently depends on `Classical.choice` since `Permutation.ofFn` and `Array.getElem_ofFn` do.
-/
@[simp]
theorem get_ofFn (f : Fin n → Fin n) (f_inj : ∀ i j, f i = f j → i = j) (i : Nat) {hi : i < n} : (ofFn f f_inj)[i] = f ⟨i,hi⟩ :=
  show (Array.ofFn f)[i]'_ = f ⟨i,hi⟩
  from Array.getElem_ofFn f i _

@[simp]
theorem toFun_ofFn (f : Fin n → Fin n) (f_inj : ∀ i j, f i = f j → i = j) : (ofFn f f_inj).toFun = f :=
  funext fun i => get_ofFn f f_inj i.1

/--
The identity permutation.

:::note warn
The function currently depends on `Classical.choice` since `Array.nodup_ofFn` does
:::
-/
@[inline]
protected def id : Permutation n :=
  ofFn id fun _ _ => id

/--
This is not `[simp]` attributed intentionally.
See `Permutation.get_one`.
-/
theorem get_id (i : Nat) {hi : i < n} : (Permutation.id (n:=n))[i] = ⟨i,hi⟩ :=
  get_ofFn id _ i

/--
This is not `[simp]` attributed intentionally.
See `Permutation.toFun_one`.
-/
theorem toFun_id : (Permutation.id (n:=n)).toFun = id :=
  toFun_ofFn id _

/--
Composition of permutations.

:::note warn
The function currently depends on `Classical.choice` since `Array.nodup_ofFn` does.
:::
-/
@[inline]
def comp (x y : Permutation n) : Permutation n :=
  ofFn (fun i => x[y[i.1].1]) fun i j h =>
    y.get_inj' i j <| x.get_inj' y[i.1] y[j.1] h

/--
This is not `[simp]` attributed intentionally.
See `Permutation.get_mul`.
-/
theorem get_comp (x y : Permutation n) (i : Nat) {h : i < n} : (x.comp y)[i] = x[y[i].1] := by
  dsimp [comp]; exact get_ofFn ..

/--
This is not `[simp]` attributed intentionally.
See `Permutation.toFun_mul`.
-/
theorem toFun_comp (x y : Permutation n) : (x.comp y).toFun = x.toFun ∘ y.toFun :=
  funext fun i => get_comp x y i.1

/--
The inverse permutation.

:::note warn
The function currently depends on `Classical.choice` since `Array.nodup_ofFn` does.
-/
@[inline]
def inv (x : Permutation n) : Permutation n :=
  ofFn (Fin.invOfInj x.toFun x.toFun_inj) fun i j h => by
    have := congrArg x.toFun h
    simp only [Fin.invOfInj_right] at this
    exact this


/-! ### The Group structure on `Permutation n` -/

instance one : OfNat (Permutation n) (nat_lit 1) := ⟨Permutation.id⟩
instance mul : Mul (Permutation n) := ⟨comp⟩

@[simp] theorem id_eq : (Permutation.id (n:=n)) = 1 := rfl
@[simp] theorem comp_eq (x y : Permutation n) : x.comp y = x * y := rfl

@[simp]
theorem get_one (i : Nat) {hi : i < n} : (1 : Permutation n)[i] = ⟨i,hi⟩ :=
  get_id i

@[simp]
theorem toFun_one : (1 : Permutation n).toFun = id :=
  toFun_id

@[simp]
theorem get_mul (x y : Permutation n) (i : Nat) {hi : i < n} : (x * y)[i] = x[y[i].1] :=
  get_comp x y i

@[simp]
theorem toFun_mul (x y : Permutation n) : (x * y).toFun = x.toFun ∘ y.toFun :=
  toFun_comp x y

@[simp]
theorem one_mul (x : Permutation n) : 1 * x = x :=
  ext _ _ fun i hi => by rw [get_mul, get_one]

@[simp]
theorem mul_one (x : Permutation n) : x * 1 = x :=
  ext _ _ fun i hi => by rw [get_mul, get_one]

@[simp]
theorem mul_assoc (x y z : Permutation n) : x * y * z = x * (y * z) :=
  ext _ _ fun i hi => by simp only [get_mul]

@[simp]
theorem inv_mul (x : Permutation n) : x.inv * x = 1 :=
  eq_of_toFun_eq _ _ <| by
    simp only [toFun_mul, inv, toFun_ofFn, toFun_one]
    apply funext; intro i; dsimp
    exact Fin.invOfInj_left ..

@[simp]
theorem mul_inv (x : Permutation n) : x * x.inv = 1 :=
  eq_of_toFun_eq _ _ <| by
    simp only [toFun_mul, inv, toFun_ofFn, toFun_one]
    apply funext; intro i; dsimp
    exact Fin.invOfInj_right ..

end Permutation

