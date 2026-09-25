import Mathlib

/-
# A question about maximal ideals

Let `I = (5, 1 + √11)` in the ring `R = ℤ[√11]`.

Show that `I` is a maximal ideal of `R`.
-/

/-
In Mathlib, `ℤ√d` is the ring `ℤ[√d]`. Thus, `ℤ√2` is `ℤ[√2]`. This is an
abbreviation for `Zsqrtd`
-/

abbrev R := ℤ√11

def sqrt11 : R := Zsqrtd.sqrtd

notation "√11" => sqrt11

namespace Z11calculations

def a : R := ⟨5, 3⟩ -- This is `5 + 3√11`

def b : R := 1 + 2 * √11 -- A user-friendly way to express `1 + 2√11`.

/-
# Exercise:

Replace the `sorry`s in brackets below with numbers and the `by sorry` with
`by rfl`.

Note, you can also get Lean to perform the calculation by using

`#eval a + b` or `#eval a * b`.
-/

example : a + b = ⟨sorry, sorry⟩ := by sorry

example : a * b = sorry := by sorry

end Z11calculations

def I : Ideal R := Ideal.span {5, 1 + √11}

abbrev F := ZMod 5

local instance : Fact (Nat.Prime 5) := by decide

def φ : R → F := by
  rintro ⟨a, b⟩
  exact a - b

example : φ (4 + 3 * √11) = 1 := by rfl

def f : R →+* F where
  toFun := φ
  map_one' := by
    simp [φ]
  map_mul' := by
    intro a b
    have h1 : (11 : F) = (1 : F) := by decide
    simp [φ, h1]
    ring
  map_zero' := by
    simp [φ]
  map_add' := by
    intro a b
    simp [φ]
    ring

lemma ker_sub_I : RingHom.ker f ≤ I := by
  rintro (⟨a, b⟩) hx
  change (f ⟨a, b⟩) = 0 at hx
  dsimp [f, φ] at hx
  rw_mod_cast [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_def] at hx
  rcases hx with ⟨c, hc⟩
  have ha : a = 5 * c + b := by
    linarith
  rw [I, Ideal.mem_span_pair]
  use c, b
  rw [ha]
  ext
  · have h1 : 1 + √11.re = (1 : ℤ) := by decide
    simp [h1]
    ring
  · have h1 : √11.im = (1 : ℤ) := by decide
    simp [h1]

lemma I_sub_ker : I ≤ RingHom.ker f := by
  intro r hr
  rw [I, Ideal.mem_span_pair] at hr
  rcases hr with ⟨a, b, rfl⟩
  change f (a * 5 + b * (1 + √11)) = 0
  dsimp [f, φ]
  have h1 : 1 + √11.re = (1 : F) := by decide
  have h2 : √11.im = (1 : F) := by decide
  have h3 : (11 : F) = 1 := by decide
  have h4 : (5 : F) = 0 := by decide
  simp [h1, h2, h3, h4]

lemma ker_eq_I : RingHom.ker f = I := by
  apply le_antisymm
  · exact ker_sub_I
  · exact I_sub_ker

lemma surjective_f : Function.Surjective f := by
  rintro z
  use Zsqrtd.ofInt z.val
  simp

example : I.IsMaximal := by
  rw [←ker_eq_I]
  apply RingHom.ker_isMaximal_of_surjective
  exact surjective_f
