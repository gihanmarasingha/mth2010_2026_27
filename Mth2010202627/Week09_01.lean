import Mathlib

variable {R} {S} {T} [CommRing R] [CommRing S] [CommRing T]

namespace exercises

/-
# Exercise

Let `R` be a ring and let `a : R`. Show that the set `{a * m | m : R}` is an
ideal of `R`.
-/

def principal (a : R) : Ideal R where
  carrier := {a * m | m : R}
  add_mem' := by
     rintro r₁ r₂ ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
     show ∃ m, a * m = r₁ + r₂
     use m₁ + m₂
     rw [←hm₁, ←hm₂]
     ring
  zero_mem' := by  sorry
  smul_mem' := by sorry

-- `f` is a ring homomorphism
variable (f : R →+* S)

def ker := {r : R | f r = 0}

/-
# Exercise

Show that the kernel of a ring homomorphism is an ideal.
-/

def ker_ideal : Ideal R where
  carrier := ker f
  add_mem' := by
    sorry
  zero_mem' := by
    sorry
  smul_mem' := by
    sorry

def im := {f r | r : R}

/-
# Exercise

Show that the image of a ring homomorphism is a Subring of S.
-/

def im_ideal : Subring S where
  carrier := im f
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-
# Exercise

Show that the composite of two ring homomorphisms is a ring homomorphism
-/

variable (g : S →+* T)

def comp_hom : R →+*T where
  toFun := sorry
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

end exercises
