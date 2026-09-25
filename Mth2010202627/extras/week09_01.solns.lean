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
    calc v.f (a + b) ≥ min (v.f a) (v.f b) := by apply v.map_add_ge_min
    _ ≥ 0 := by exact le_min ha hb -- Found using `apply?`
  zero_mem' := by
    show v.f 0 ≥ 0
    have hz : v.f (0 : K) = ⊤ := by rw [v.top_iff_zero]
    rw [hz]
    exact OrderTop.le_top 0
  neg_mem' := by
    intro a (ha : v.f a ≥ 0)
    show v.f (-a) ≥ 0
    have h : -a = (-1) * a := by exact neg_eq_neg_one_mul a
    rw [h]
    rw [v.map_mul]
    rw [neg_one_val, zero_add]
    exact ha

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
`valZ x⁻¹ = - valZ x` for `x : Kˣ`. Here, `x⁻¹` is the inverse of `x`.
Type `⁻¹` as `\-1`.
-/
lemma val_invZ {x : Kˣ} : v.valZ x⁻¹ = -v.valZ x := by
  have h : 0 = v.valZ x + v.valZ x⁻¹ :=
    calc 0 = v.valZ 1 := by rw [one_valZ]
    _ = v.valZ (x * x⁻¹) := by simp
    _ = v.valZ x + v.valZ x⁻¹ := by rw [valZ_mul]
  linarith

/--
`f x⁻¹ = f x`
-/
lemma val_inv {x : K} (hnz : x ≠ 0) : v.f x⁻¹ = - v.f x := by
  have h : 0 = v.f x + v.f x⁻¹ :=
    calc 0 = v.f 1 := by rw [one_val]
    _ = v.f (x * x⁻¹) := by rw [mul_inv_cancel₀ hnz]
    _ = v.f x + v.f x⁻¹ := by rw [v.map_mul]
  rcases (ne_zero_val_int v hnz) with ⟨n, hn⟩
  rcases (ne_zero_val_int v (inv_ne_zero hnz)) with ⟨m, hm⟩
  have hnmsump : 0 = (n : WithTop ℤ) + (m : WithTop ℤ) := by
    simpa [hn, hm] using h
  have hnmsum : 0 = n + m := by
    exact_mod_cast hnmsump
  have hmneg : m = -n := by linarith
  rw [hm, hn, hmneg]
  norm_cast

/--
For every `x ≠ 0`, either `x ∈ vring` or `x⁻¹ in vring`.
-/
lemma mem_or_inv_mem {x : K} (h : x ≠ 0) :
    x ∈ (vring v).carrier ∨ x⁻¹ ∈ (vring v).carrier := by
  rw [or_iff_not_imp_left]
  intro hxnot
  show v.f x⁻¹ ≥ 0
  contrapose! hxnot
  show v.f x ≥ 0
  rw [val_inv v h] at hxnot
  rcases (ne_zero_val_int v h) with ⟨n, hn⟩
  have h1t : -(n : WithTop ℤ) < 0 := by rwa [←hn]
  have h1 : -n < 0 := by exact_mod_cast h1t
  have h2 : n ≥ 0 := by linarith
  have h2t : (n : WithTop ℤ) ≥ 0 := by exact_mod_cast h2
  rwa [hn]

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
  have rnn : v.f r ≥ 0 := r.property
  constructor
  · rintro ⟨s, hs⟩
    have myeq : r.1 * s.1 = 1 := by
      exact_mod_cast hs
    have rnz : r.1 ≠ 0 := by
      intro req
      rw [req, zero_mul] at myeq
      exact zero_ne_one myeq
    have snz : s.1 ≠ 0 := by
      intro seq
      rw [seq, mul_zero] at myeq
      exact zero_ne_one myeq
    rcases (ne_zero_val_int v rnz) with ⟨n, hn⟩
    rcases (ne_zero_val_int v snz) with ⟨m, hm⟩
    have rssum : v.f r + v.f s = 0 :=
      calc v.f r + v.f s = v.f (r * s) := by rw [v.map_mul]
      _ = v.f 1 := by norm_cast; rw [hs]; norm_cast
      _ = 0 := by rw [one_val]
    have nmsump : (n : WithTop ℤ) + m = 0 := by simpa [hn, hm] using rssum
    have nmsum : n + m = 0 := mod_cast nmsump
    have hnnn : n ≥ 0 := by simpa [hn] using rnn
    have hss : v.f s ≥ 0 := s.property
    have hmnn : m ≥ 0 := by simpa [hm] using hss
    have hnzero : n = 0 := by linarith
    simpa [hnzero] using hn
  intro vrzero
  have rnzero : (r :  K) ≠ 0 := by
    by_contra!
    rw [←v.top_iff_zero] at this
    have zeq : (0 : WithTop ℤ) = ⊤ := by
      rw [←vrzero, this]
    exact WithTop.zero_ne_top zeq
  have h_inv0 : v.f ((r : K)⁻¹) = 0 := by
    have h := v.val_inv (x := (r : K)) rnzero
    simpa [vrzero] using h
  have hr_inv_nonneg : v.f ((r : K)⁻¹) ≥ 0 := by simp [h_inv0]
  let rinv : vring v := ⟨(r : K)⁻¹, hr_inv_nonneg⟩
  have h1 : r * rinv = (1 : v.vring) := by
    ext
    simp [rinv, rnzero]
  use rinv

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
  constructor
  · intro hx
    have hZ0 : v.valZ x = 0 := (v.mem_ker_iff_valZ x).mp hx
    have hx0 : v.f (x : K) = 0 := by simpa [hZ0] using v.valZ_spec x
    have hx_nonneg : v.f (x : K) ≥ 0 := by simp [hx0]
    have hx_inv0 : v.f ((x : K)⁻¹) = 0 := by
      have := v.val_inv (x := (x : K)) x.ne_zero
      simpa [hx0] using this
    have hx_inv_nonneg : v.f ((x : K)⁻¹) ≥ 0 := by simp [hx_inv0]
    let r : v.vring := ⟨(x : K), hx_nonneg⟩
    let rinv : v.vring := ⟨(x : K)⁻¹, hx_inv_nonneg⟩
    let u : (v.vring)ˣ :=
      { val := r
        inv := rinv
        val_inv := by
          ext
          simp [r, rinv]
        inv_val := by
          ext
          simp [r, rinv, mul_comm] }
    refine ⟨u, ?_⟩
    ext
    simp [vringUnitsToUnits, u, r]
  · intro hx
    rcases hx with ⟨u, rfl⟩
    let r : v.vring := (u : v.vring)
    have hunit : ∃ s : v.vring, r * s = 1 := by
      refine ⟨(u⁻¹ : (v.vring)ˣ), ?_⟩
      have h := u.mul_inv      -- u * u⁻¹ = 1 in units
      simp [r]
    have hr0 : v.f (r : K) = 0 := (v.vring_unit r).mp hunit
    have hx0 : v.f (vringUnitsToUnits v u : K) = 0 := by
      simpa [vringUnitsToUnits] using hr0
    have hZ0 : v.valZ (vringUnitsToUnits v u) = 0 := by
      have hspec := v.valZ_spec (vringUnitsToUnits v u)
      have : (v.valZ (vringUnitsToUnits v u) : WithTop ℤ)
             = (0 : WithTop ℤ) := by
        simpa [hspec] using hx0
      exact_mod_cast this
    have : vringUnitsToUnits v u ∈ v.valZ_hom.ker :=
      (v.mem_ker_iff_valZ (vringUnitsToUnits v u)).mpr hZ0
    simpa using this

lemma vfsurj : Surjective (valZ v) := by
  intro y
  obtain ⟨r, hr⟩ := v.surj y
  have rnz : r ≠ 0 := by
    intro req
    rw [←v.top_iff_zero r] at req
    have : y ≠ (⊤ : WithTop ℤ) := by exact WithTop.coe_ne_top
    apply this
    rwa [←hr]
  let u := Units.mk0 r rnz
  use u
  change v.valZ u = y
  have hr' : v.f u = y := by simpa [u] using hr
  have hspec : v.f u = v.valZ u := v.valZ_spec u
  have hcoeq : v.valZ u = y := by simpa [hspec] using hr'
  rw [←WithTop.coe_eq_coe]
  norm_cast

lemma range_eq : Surjective v.valZ_hom := by
  intro y
  set yz := Multiplicative.toAdd y with hz
  obtain ⟨a, ha⟩ := vfsurj v yz
  use a
  simpa [valZ_hom]

noncomputable def field_units_quotient_ring_units :
    Kˣ ⧸ (vringUnitsSubgroup v) ≃* Multiplicative ℤ := by
  rw [←ker_eq]
  exact QuotientGroup.quotientKerEquivOfSurjective v.valZ_hom v.range_eq

end VFunc
