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

We show that `Permutation n` forms a group and provide several special permutations, namely the ***transposition*** and the ***cyclic permutation***.

## Main declarations

* `Permutation`: the structure type representig permutations on `Fin n`.
* `Permutation.id` / `Permutation.comp` / `Permutation.inv`: the group structure on `Permutation n`.
* `Permutation.transpos`: the transposition
* `Permutation.cyclic`: the cyclic permutation

## TODO

* Write and prove the theorem that specifies `Permutation.cyclic`.

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
  x.nodup.get_inj (hi:=x.size_eq.symm ▸ hi) (hj:=x.size_eq.symm ▸ hj) <| h

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
:::
-/
@[inline]
def inv (x : Permutation n) : Permutation n :=
  ofFn (Fin.invOfInj x.toFun x.toFun_inj) fun i j h => by
    have := congrArg x.toFun h
    simp only [Fin.invOfInj_right] at this
    exact this

/--
`Permutation.inv.toFun x` is a left inverse to `x.toFun`; see also `Permutation.toFun_toFun_inv`.

:::note warn
The function currently depends on `Classical.choice` since `Permutation.toFun_ofFn` does.
:::
-/
@[simp]
theorem toFun_inv_toFun (x : Permutation n) (i : Fin n) : x.inv.toFun (x.toFun i) = i := by
  simp only [inv, toFun_ofFn]
  exact Fin.invOfInj_left ..

/--
`Permutation.inv.toFun x` is a right inverse to `x.toFun`; see also `Permutation.toFun_inv_toFun`.

:::note warn
The function currently depends on `Classical.choice` since `Permutation.toFun_ofFn` does.
-/
@[simp]
theorem toFun_toFun_inv (x : Permutation n) (i : Fin n) : x.toFun (x.inv.toFun i) = i := by
  simp only [inv, toFun_ofFn]
  exact Fin.invOfInj_right ..


/-! ### Declarations about `Permutation.restriction` -/

/--
Restrict a permutation `x : Permutation n` to `Fin m` provided `m ≤ n` and the support of `x` lies in `Fin m` under the canonical embedding `Fin.castLE`.

:::note warn
The function depends on `Classical.choice` because of `Array.getElem_pmap`.
:::
-/
@[inline]
def restrict {m : Nat} (hle : m ≤ n) (x : Permutation n) (h : ∀ (i : Fin n), m ≤ i → x[i.1] = i) : Permutation m where
  val := (x.val.shrink m).pmap (p := fun i => i.1 < m)
    (fun i hi => ⟨i.1,hi⟩)
    fun i hi => by
      dsimp
      rewrite [x.val.getElem_shrink (x.size_eq.symm ▸ hle)]
      apply Decidable.by_contra
      simp only [Nat.not_lt]
      intro hm
      rewrite [x.val.size_shrink (x.size_eq.symm ▸ hle)] at hi
      have hin : i < n := trans hi hle
      have : x[i]'hin = i := x.get_inj (x[i]'hin) i (h (x[i]'hin) hm)
      rw [← Nat.not_lt] at hm
      exact hm (trans this hi)
  size_eq := by
    simp only [Array.size_pmap, x.val.size_shrink (x.size_eq.symm ▸ hle)]
  nodup := by
    apply Array.nodup_of_get_inj
    intro i j hi hj
    simp only [Array.getElem_pmap]
    intro hx
    conv at hi =>
      simp only [Array.size_pmap, x.val.size_shrink (x.size_eq.symm ▸ hle)]
    conv at hj =>
      simp only [Array.size_pmap, x.val.size_shrink (x.size_eq.symm ▸ hle)]
    have := congrArg Fin.val hx
    conv at this =>
      simp only [x.val.getElem_shrink (x.size_eq.symm ▸ hle)]
      change (x[i]'(trans (r:=LT.lt (α:=Nat)) hi hle)).1 = (x[j]'(trans (r:=LT.lt (α:=Nat)) hj hle)).1
    exact x.get_inj i j <| Fin.eq_of_val_eq this


/-! ### Declarations about `Permutation.castAdd` -/

/--
`Permutation.castAdd x` embeds the permutation `x : Permutation n` on `Fin n` into one on `Fin (n+m)`.

:::note warn
The function currently depends on `Classical.choice` since a lot of stuff do.
:::
-/
@[inline]
def castAdd (m : Nat) (x : Permutation n) : Permutation (n+m) where
  val :=
    x.val.map (Fin.castAdd (m:=m))
    ++ Array.ofFn fun (i : Fin m) => (i.addNat n).cast (Nat.add_comm m n)
  size_eq := by
    rw [Array.size_append, Array.size_map, x.size_eq, Array.size_ofFn]
  nodup := by
    refine Array.nodup_append ?_ ?_ ?_
    . apply Array.nodup_map _ _ x.nodup
      intro i j h
      cases i; cases j; cases h; rfl
    . apply Array.nodup_ofFn
      intro i j h
      cases i; cases j
      have h := congrArg Fin.val h
      dsimp at h
      cases Nat.add_right_cancel h
      rfl
    . intro i j hi hj
      rewrite [Array.getElem_map, Array.getElem_ofFn]
      intro h
      have h := congrArg Fin.val h
      conv at hi => simp only [Array.size_map, x.size_eq]
      conv at h =>
        dsimp [Fin.castAdd]; change x[i]'hi = j+n
      have := calc
        x[i].1 < n := x[i].2
        _      ≤ j+n := Nat.le_add_left n j
      exact (Nat.lt_irrefl x[i].val) (h.symm ▸ this)

/--
:::note warn
The function currently depends on `Classical.choice` since `Array.getElem_append_let` and `Array.getElem_map` do.
:::
-/
theorem get_castAdd_lt (m : Nat) (x : Permutation n) (i : Nat) {hi : i < n + m} (h : i < n) : (x.castAdd m)[i] = x[i].castAdd m := by
  unfold castAdd GetElem.getElem
  simp only [instGetElemPermutationNatFinLtInstLTNat]
  have : i < x.val.size := x.size_eq.symm ▸ h
  rewrite [Array.getElem_append_left _ _ ((Array.size_map _ _).symm ▸ this)]
  rw [Array.getElem_map]

/--
:::note warn
The function currently depends on `Classical.choice` since `Array.getElem_append_right` and `Array.getElem_ofFn` do.
:::
-/
theorem get_castAdd_ge (m : Nat) (x : Permutation n) (i : Nat) {hi : i < n + m} (h : i ≥ n) : (x.castAdd m)[i] = ⟨i,hi⟩ := by
  unfold castAdd GetElem.getElem
  simp only [instGetElemPermutationNatFinLtInstLTNat]
  have : i ≥ x.val.size := x.size_eq.symm ▸ h
  rewrite [Array.getElem_append_right _ _ ((Array.size_map _ _).symm ▸ this)]
  rewrite [Array.getElem_ofFn]
  apply Fin.eq_of_val_eq
  simp only [Array.size_map, Fin.addNat_mk, Fin.cast_mk, x.size_eq]
  exact Nat.sub_add_cancel h

/--
:::note warn
The function currently depends on `Classical.choice` since `Permutation.get_castAdd_lt` and `Permutation.get_castAdd_ge` do.
:::
-/
theorem get_castAdd_ite (m : Nat) (x : Permutation n) (i : Nat) {hi : i < n + m} : (x.castAdd m)[i] = if h : i < n then x[i].castAdd m else ⟨i,hi⟩ := by
  if h : i < n then
    rewrite [dif_pos h]; exact x.get_castAdd_lt m i h
  else
    rewrite [dif_neg h]; exact x.get_castAdd_ge m i (Nat.le_of_not_lt h)


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
    funext i; simp only [toFun_mul, toFun_one]
    exact toFun_inv_toFun x i

@[simp]
theorem mul_inv (x : Permutation n) : x * x.inv = 1 :=
  eq_of_toFun_eq _ _ <| by
    funext i; simp only [toFun_mul, toFun_one]
    exact toFun_toFun_inv x i

theorem mul_left_cancel {x y z : Permutation n} (h : x * y = x * z) : y = z := by
  have := congrArg (x.inv * ·) h
  conv at this =>
    dsimp; simp only [← mul_assoc, inv_mul, one_mul]
  exact this

theorem mul_right_cancel {x y z : Permutation n} (h : x * z = y * z) : x = y := by
  have := congrArg (· * z.inv) h
  conv at this =>
    dsimp; simp only [mul_assoc, mul_inv, mul_one]
  exact this

theorem mul_inv_eq_of_eq_mul {x y z : Permutation n} (h : x = z * y) : x * y.inv = z := by
  have := congrArg (· * y.inv) h
  conv at this => dsimp; rewrite [mul_assoc, mul_inv, mul_one]
  exact this

theorem inv_mul_eq_of_mul_eq {x y z : Permutation n} (h : y * x = z) : x = y.inv * z := by
  have := congrArg (y.inv * ·) h
  conv at this => dsimp; rewrite [← mul_assoc, inv_mul, one_mul]
  exact this

theorem eq_inv_of_mul_eq_left (x y : Permutation n) (h : x * y = 1) : y = x.inv := by
  have := congrArg (x.inv * ·) h
  conv at this =>
    dsimp; rewrite [← mul_assoc, inv_mul, one_mul, mul_one]
  exact this

theorem eq_inv_of_mul_eq_right (x y : Permutation n) (h : x * y = 1) : x = y.inv := by
  have := congrArg (· * y.inv) h
  conv at this =>
    dsimp; rewrite [mul_assoc, mul_inv, one_mul, mul_one]
  exact this

instance powNat : Pow (Permutation n) Nat where
  pow x k :=
    let rec go : Nat → Permutation n
    | 0 => 1
    | (k+1) => x * go k
    go k

@[simp]
theorem powNat_zero (x : Permutation n) : x^0 = 1 :=
  rfl

@[simp]
theorem powNat_succ (x : Permutation n) (k : Nat) : x^(k+1) = x * x^k :=
  rfl

@[simp]
theorem powNat_add (x : Permutation n) (k l : Nat) : x^(k+l) = x^k * x^l := by
  induction k with
  | zero =>
    simp only [Nat.zero_eq, Nat.zero_add, powNat_zero, one_mul]
  | succ k IH =>
    simp only [Nat.succ_add, powNat_succ]
    rw [mul_assoc, IH]

instance powInt : Pow (Permutation n) Int where
  pow x k := match k with
    | .ofNat k => x^k
    | .negSucc k => x.inv ^ (k+1)


/-! ### Transpositions -/

/-- `Permutation.swap x i j` swaps the images of `i` and `j` of a permutation `x`. -/
@[inline]
def swap (x : Permutation n) (i j : Fin n) : Permutation n where
  val := x.val.swap (i.cast x.size_eq.symm) (j.cast x.size_eq.symm)
  size_eq := (x.val.size_swap _ _).trans x.size_eq
  nodup := x.val.nodup_swap _ _ x.nodup

theorem get_swap (x : Permutation n) (i j : Fin n) (k : Nat) {hk : k < n} : (x.swap i j)[k] = if j.1 = k then x[i.1] else if i.1 = k then x[j.1] else x[k] :=
  show (x.val.swap _ _)[k]'_ = _ by
    simp only [Array.getElem_swap, Fin.cast]; rfl

theorem swap_comm (x : Permutation n) (i j : Fin n) : x.swap i j = x.swap j i :=
  Permutation.eq _ _ <| Array.swap_comm ..

theorem swap_swap_same (x :Permutation n) (i j : Fin n) : (x.swap i j).swap i j = x :=
  ext _ _ fun k hk => by
    simp only [get_swap, if_pos]
    apply dite (j.1 = k) <;> apply dite (i.1 = k) <;> intro hik hjk
    all_goals simp only [hik, hjk, if_pos, if_neg]
    rw [if_neg (Ne.symm hik)]

/-- The transposition; i.e. `Permutation.transpos i j` is the permutation which swaps `i` and `j` and leaves the others. -/
@[inline]
def transpos (i j : Fin n) : Permutation n :=
  swap 1 i j

theorem transpos_comm (i j : Fin n) : transpos i j = transpos j i :=
  swap_comm 1 i j

theorem get_transpos (i j : Fin n) (k : Nat) {hk : k < n} : (transpos i j)[k] = if j.1 = k then i else if i.1 = k then j else ⟨k,hk⟩ := by
  simp only [transpos, get_swap, get_one]

theorem mul_transpose_eq_swap (x : Permutation n) (i j : Fin n) : x * (transpos i j) = x.swap i j :=
  ext _ _ fun k hk => by
    simp only [get_mul, get_transpos, get_swap]
    if hjk : j.1 = k then
      cases hjk; simp only [if_pos]
    else if hik : i.1 = k then
      cases hik; simp only [if_neg hjk, if_pos]
    else
      simp only [if_neg hjk, if_neg hik]

/-- The transposition is of order 2. -/
@[simp]
theorem transpos_mul_transpos_same (i j : Fin n) : transpos i j * transpos i j = 1 := by
  rewrite [mul_transpose_eq_swap]; dsimp [transpos]
  exact swap_swap_same 1 i j

@[simp]
theorem inv_transpos (i j : Fin n) : (transpos i j).inv = transpos i j :=
  Eq.symm <| eq_inv_of_mul_eq_left _ _ <| transpos_mul_transpos_same i j

/-- Any conjugate of a transposition is again a transposition. -/
theorem transpos_conj (i j : Fin n) (x : Permutation n) : x * transpos i j * x.inv = transpos x[i.1] x[j.1] :=
  mul_inv_eq_of_eq_mul <| ext _ _ fun k hk => by
    simp only [get_mul, get_transpos]
    if hjk : j.1 = k then
      cases hjk; simp only [if_pos]
    else
      have : x[j.1].1 ≠ x[k].1 :=
        fun h => hjk <| x.get_inj _ _ (Fin.eq_of_val_eq h)
      simp only [hjk, this, if_neg]
      if hik : i.1 = k then
        cases hik; simp only [if_pos]
      else
        have : x[i.1].1 ≠ x[k].1 :=
          fun h => hik <| x.get_inj _ _ (Fin.eq_of_val_eq h)
        simp only [hik, this, if_neg]

/-- Adjacent transposition; i.e. a transposition of consecutive numbers -/
@[inline]
def transposAdj (i : Nat) (h : i+1 < n) : Permutation n :=
  transpos ⟨i, Nat.lt_of_succ_lt h⟩ ⟨i+1,h⟩

@[simp]
theorem get_transposAdj_self {i : Nat} {h : i+1 < n} {h' : i < n} : (transposAdj i h)[i]'h' = ⟨i+1,h⟩ := by
  simp only [transposAdj, get_transpos, i.succ_ne_self, if_neg, if_pos]

@[simp]
theorem get_transAdj_succ {i : Nat} {h : i+1 < n} : (transposAdj i h)[i+1] = ⟨i,Nat.lt_of_succ_lt h⟩ := by
  simp only [transposAdj, get_transpos, if_pos]

theorem get_transposAdj_of_lt {i : Nat} {h : i+1 < n} {j : Nat} (hj : j < i) {hj' : j < n} : (transposAdj i h)[j]'hj' = ⟨j,hj'⟩ := by
  simp only [transposAdj, get_transpos]
  simp only [Nat.ne_of_gt <| .step hj, Nat.ne_of_gt hj, if_neg]

theorem get_transposAdj_of_gt {i : Nat} {h : i+1 < n} {j : Nat} {hj : j > i+1} {hj' : j < n} : (transposAdj i h)[j]'hj' = ⟨j,hj'⟩ := by
  simp only [transposAdj, get_transpos]
  simp only [Nat.ne_of_lt hj, Nat.ne_of_lt <| Nat.lt_of_succ_lt hj, if_neg]


/-! ### Cyclic permutation -/

/--
Construct a cyclic permutation;
i.e. Given `l : List (Fin n)`, `Permutation.cyclic l` is the permutation on `Fin n` such that it sends `l[i] ↦ l[i+1]` for `i < l.length-1` and `l[l.length-1] ↦ l[0]` and leaves the elements outside of `l`.

:::note warn
Although the function does not require `l.Nodup`, the result may be meaningless otherwise.
:::
-/
@[inline]
def cyclic (l : List (Fin n)) : Permutation n :=
  match l with
  | [] => 1
  | (i :: l) => l.foldr (fun j x => x.swap i j) 1

theorem get_cyclic_not_mem (l : List (Fin n)) (i : Fin n) (h : i ∉ l) : (cyclic l)[i.1] = i := by
  cases l with
  | nil => exact get_one i.1
  | cons j l =>
    dsimp [cyclic]
    simp only [List.mem_cons, not_or] at h
    suffices ∀ (y : Permutation n), (l.foldr _ y)[i.1] = y[i.1] by
      rewrite [this 1]; exact get_one i.1
    induction l with
    | nil => intros; rfl
    | cons k l IH =>
      intro y
      simp only [List.mem_cons, not_or] at h 
      specialize IH ⟨h.1,h.2.2⟩ y
      dsimp only [List.foldr]
      rewrite [get_swap, if_neg (Fin.val_ne_of_ne <| Ne.symm h.2.1), if_neg (Fin.val_ne_of_ne <| Ne.symm h.1)]
      exact IH


/-! ### Order reversion -/

/--
`Fin.rev` as a permutation; hence, it permutes a sequence `(a₁,a₂,…,aₙ)` into `(aₙ,…,a₂,a₁)`.
-/
@[inline]
def rev (n : Nat) : Permutation n :=
  Permutation.ofFn Fin.rev fun _ _ => Fin.rev_inj.mp

end Permutation

