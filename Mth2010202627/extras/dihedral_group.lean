import Mathlib.GroupTheory.SpecificGroups.Dihedral

variable {n : Nat} [NeZero n]

open DihedralGroup

abbrev D (n : Nat) := DihedralGroup n

-- def H (_ : DihedralGroup n) (k : Nat): Subgroup (D n) := Subgroup.zpowers (r k)

def myhom {k : Nat} (h : k ∣ n) : DihedralGroup n →* DihedralGroup k where
  toFun := fun g => match g with
  | r i => r (ZMod.cast i)
  | sr i => sr (ZMod.cast i)
  map_one' := by
    have : (1 : DihedralGroup n) = r (0 : ZMod n) := by simp
    rw [this]
    simp
  map_mul' := by
    intro x y
    cases x <;> cases y <;> simp [ZMod.cast_add h, ZMod.cast_sub h]

lemma ne_zero_of_dvd {k} (h : k ∣ n) : k ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne n) h

lemma ZMod.cast_cast {k} (h : k ∣ n) (i : ZMod k) :
    ((ZMod.cast (ZMod.cast i : ZMod n)) : ZMod k) = i := by
  haveI : NeZero k := ⟨ne_zero_of_dvd h⟩
  apply cast_cast_zmod_of_le
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (NeZero.ne n)  -- from [NeZero n] get 0 < n
  · exact h

lemma myhom_surjective {k : Nat} (h : k ∣ n) : Function.Surjective (myhom h) := by
  intro g
  cases g with
  | r i =>
      use r (ZMod.cast i)
      simp [myhom]
      apply ZMod.cast_cast h
  | sr i =>
      use sr (ZMod.cast i)
      simp [myhom]
      apply ZMod.cast_cast h
