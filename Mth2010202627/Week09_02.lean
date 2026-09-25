import Mathlib

/-
# Formalisation of Coursework 3, MTH2010 2025
-/

open Function

/--
A function defined on `K`. This is slighly different to the function presented
in the coursework sheet. Lean would struggle to work with addition on the
multiplicative group `Kˣ`. Instead, we define a function `K → ℤ ∪ {∞}`. In Lean,
`ℤ ∪ {∞}` is represented as `WithTop ℤ` and `∞` is written `⊤`, typed `\top`.

The function `f` is surjective and satisfies a kind of homomorphism property
(except that `WithTop ℤ` isn't an additive group). We have `f = ⊤` exactly when
`x = 0`. Finally, `f (x + y) ≥ min (f(x), f(y))`.
-/
structure VFunc (K : Type*) [Field K] where
  f : K → WithTop ℤ
  top_iff_zero : ∀ x, f x = ⊤ ↔ x = 0
  surj : f.Surjective
  map_mul : ∀ x y, f (x * y) = f x + f y
  map_add_ge_min : ∀ x y, f (x + y) ≥ min (f x) (f y)

namespace VFunc

/-
`K` is a vield and `v` is a 'function' of the type `VFunc`. In future, we will
always use this `v`. Note the acutal function is `v.f`
-/

variable {K} [Field K] (v : VFunc K)

/-
## Auxiliary results
-/

/--
For every non-zero element of `K`, there exists an integer `n` such that
`f x = n`. This result is useful in extracting an integer value for `f x`
rather than a value of `WithTop ℤ`.

It is usually easier to use the function `valZ` instead.
-/
lemma ne_zero_val_int {x : K} (hxnz : x ≠ 0) : ∃ (n : ℤ), v.f x = n := by
  have hne : v.f x ≠ ⊤ := by
    intro h
    rw [v.top_iff_zero] at h
    exact hxnz h
  exact Option.ne_none_iff_exists'.mp hne

/--
For `x : Kˣ`, this returns the integer value that corresponds to `f x`.
Here, `Kˣ` is the group of units of `K`. Type `ˣ` as `\^x`.
-/
noncomputable def valZ (x : Kˣ) : ℤ :=
  Classical.choose (v.ne_zero_val_int (by exact x.ne_zero))

/--
`f x = valZ x`, for `x : Kˣ`.
-/
lemma valZ_spec (x : Kˣ) :
    v.f (x : K) = (v.valZ x : WithTop ℤ) :=
  Classical.choose_spec (v.ne_zero_val_int (x.ne_zero))

/--
`valZ (x * y) = valZ x + valZ y`, for `x y : Kˣ`.
-/
lemma valZ_mul (x y : Kˣ) :
    v.valZ (x * y) = v.valZ x + v.valZ y := by
  have h_with : v.f ((x * y : Kˣ) : K)
      = v.f (x : K) + v.f (y : K) := by
    simpa using v.map_mul (x : K) (y : K)
  have h_with' :
      (v.valZ (x * y) : WithTop ℤ)
        = (v.valZ x : WithTop ℤ) + (v.valZ y : WithTop ℤ) := by
    repeat rw [←valZ_spec]
    assumption
  exact_mod_cast h_with'

/--
`valZ 1 = 0`
-/
lemma one_valZ : v.valZ 1 = 0 := by
  have hf : v.valZ 1 + v.valZ 1 = v.valZ 1 :=
    calc v.valZ 1 + v.valZ 1 = v.valZ (1 * 1) := by rw [valZ_mul]
    _ = v.valZ 1 := by norm_num
  linarith

/--
`f 1 = 0`
-/
lemma one_val : v.f (1 : K) = 0 := by
  have h := v.valZ_spec (1 : Kˣ)
  have hz : v.valZ (1 : Kˣ) = 0 := v.one_valZ
  simpa [hz] using h

/--
`valZ (-1) = 0`
-/
lemma neg_one_valZ : v.valZ (-1) = 0 := by
  have h : v.valZ 1 = v.valZ (-1) + v.valZ (-1) :=
    calc v.valZ 1 = v.valZ ((-1) * (-1)) := by norm_num
    _ = v.valZ (-1) + v.valZ (-1) := by rw [valZ_mul]
  rw [one_valZ] at h
  linarith

/--
`f (-1) = 0`
-/
lemma neg_one_val : v.f (-1) = 0 := by
  have h := v.valZ_spec (-1 : Kˣ)
  have hz : v.valZ (-1 : Kˣ) = 0 := v.neg_one_valZ
  simpa [hz] using h

/--
`f (-x) = f(x)`
-/
lemma neg_val {x : K} : v.f (-x) = v.f x := by
  calc v.f (-x ) = v.f ((-1) * x) := by norm_num
    _ = v.f (-1) + v.f x := by rw [v.map_mul]
    _ = 0 + v.f x := by rw [neg_one_val]
    _ = v.f x := by rw [zero_add]

/-
## Question (a)

Let `R = {x ∈ Kˣ : f(x) ≥ 0}`.

Prove that `R` is a subring of `K` which contains `1` and `-1`.
-/

/--
The set `{x : K | f x ≥ 0}` is a subring of `K`.
-/
def vring : Subring K where
  carrier := {x : K | v.f (x : K) ≥ 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at * -- Find this from `simp?`
    rw [v.map_mul]
    exact Left.add_nonneg ha hb -- Find via `apply?`
  one_mem' := by
    show v.f 1 ≥ 0
    rw [one_val]
  add_mem' := by
    intro a b (ha : v.f a ≥ 0) (hb : v.f b ≥ 0)
    show v.f (a + b) ≥ 0
    sorry
  zero_mem' := by
    show v.f 0 ≥ 0
    sorry
  neg_mem' := by
    intro a (ha : v.f a ≥ 0)
    show v.f (-a) ≥ 0
    sorry

/--
The `1` element of `vring`.
-/
def vring_one : vring v := 1

/--
The `-1` element of `vring`.
-/
def vring_neg_one : vring v := -1

/-
## Question (b)

Prove that for each element `x ∈ Kˣ`, either `x ∈ R` or `x⁻¹ ∈ R`.
-/


/--
For every `x ≠ 0`, either `x ∈ vring` or `x⁻¹ in vring`.
-/
lemma mem_or_inv_mem {x : K} (h : x ≠ 0) :
    x ∈ (vring v).carrier ∨ x⁻¹ ∈ (vring v).carrier := by
  sorry

/-
## Question (c)

Prove that `x ≠ 0 ∈ R` is a unit of `R` if and only if `f(x) = 0`. Deduce that
`(Rˣ, ×)` is a subgroup of `(Kˣ, ×)` and the quotient group `Kˣ ⧸ Rˣ` is
isomorphic to the group `(ℤ, +)`

[Hint: use surjectivtiy of `f`]
-/

/--
An element `r : vring` is a unit of `vring` if an only if `f r = 0`.
-/
lemma vring_unit (r : vring v) : (∃ (s : vring v), r * s = 1) ↔ v.f r = 0 := by
  sorry

/--
The homomorphism from `vringˣ` to `Kˣ` induced by the inclusion (subtype)
homomorphism from `vring` to `K`.
-/
def vringUnitsToUnits : (vring v)ˣ →* Kˣ :=
  Units.map (vring v).subtype

/--
The subgroup of `Kˣ` given by the image of the inclusion homomorphism from
`vringˣ` to `Kˣ`.
-/
def vringUnitsSubgroup : Subgroup Kˣ := (vringUnitsToUnits v).range

/-
The homomorphism from `Kˣ` to `ℤ` given by `valZ`. Due to the way Mathlib works,
we treat `ℤ` as a *multiplicative* group where the identity `1` is `0` and
`x * y` means `x + y`.
-/
noncomputable def valZ_hom : Kˣ →* Multiplicative ℤ where
  toFun := valZ v
  map_one' := one_valZ v
  map_mul' := valZ_mul v

/--
An application of the first isomorphism theorem. We will actualy use a modified
version of the first isomorphism theorem, but it's good to see how it's used.
-/
noncomputable def fit_app : Kˣ ⧸ v.valZ_hom.ker ≃* v.valZ_hom.range :=
  QuotientGroup.quotientKerEquivRange v.valZ_hom

/--
For `x : Kˣ`, `x` is in the kernel of `valZ_hom` if an only if `valZ x = 0`.
-/
lemma mem_ker_iff_valZ (x : Kˣ) :
  x ∈ v.valZ_hom.ker ↔ v.valZ x = 0 := by
  simp
  rfl

/--
The kernel of `valZ_hom` is the unit group
-/
lemma ker_eq : v.valZ_hom.ker = (vringUnitsSubgroup v) := by
  ext x
  sorry

lemma vfsurj : Surjective (valZ v) := by
  sorry

lemma range_eq : Surjective v.valZ_hom := by
  sorry

noncomputable def field_units_quotient_ring_units :
    Kˣ ⧸ (vringUnitsSubgroup v) ≃* Multiplicative ℤ := by
  rw [←ker_eq]
  exact QuotientGroup.quotientKerEquivOfSurjective v.valZ_hom v.range_eq

end VFunc
