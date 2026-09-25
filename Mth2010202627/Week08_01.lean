import Mathlib

/-
# Properties of Rings
-/

variable {R : Type*} [CommRing R]

/-
## Ring axioms
-/

variable (a b c : R)

example : a + b = b + a := by apply add_comm

example : a + 0 = a := by apply add_zero

example : a + (-a) = 0 := by apply add_neg_cancel

example : (a + b) + c = a + (b + c) := by apply add_assoc

example : a * b = b * a := by apply mul_comm

example : (a * b) * c = a * (b * c) := by apply mul_assoc

example : a * (b + c) = a * b + a * c := by apply left_distrib

example : a * 1 = a := by apply mul_one


/-
# Example

Complete the following proofs, adding lines of calculation as necessary.
The proof in each line should be of the form `rw [thm]`, where `thm` is
one of the axioms given above *or* one of the lemmas you've already proved while
doing this sheet.

**Note** in some cases you may need to do a rewrite in a different form, such as
* `rw [thm x y]` where the variables `x` and `y` are inputs to the theorem or
* `rw [←thm]` in which every occurrence of the right side of `thm` in the goal
  is replaced with the left side of `thm`.
* `rw [thm1, thm2]` in which you rewrite with multiple theorems.
-/

namespace examples

lemma zero_add : 0 + a = a := by
  calc
    0 + a = a + 0 := by rw [add_comm]
    _ = a := by sorry

lemma one_mul : 1 * a = a := by
  calc
    1 * a = a * 1 := by rw [mul_comm]
    _ = a := by sorry

/-
You'll may need an additional line or two of calculation to finish the next
proof.
-/

lemma right_distrib : (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := by rw [mul_comm]
    _ = a * c + b * c := by sorry

lemma neg_add_cancel : -a + a = 0 := by
  calc
    -a + a = a + -a := by rw [add_comm]
    _ = 0 := by rw [add_neg_cancel]

/-
The next result requires some thinking.
-/

lemma mul_zero : a * 0 = 0 := by
  symm
  show 0 = a * 0
  calc
    0 = (a * 0) + -(a * 0) := by rw [add_neg_cancel]
    _ = (a * (0 + 0)) + -(a * 0) := by rw [add_zero]
    _ = a * 0 := by sorry

lemma zero_mul : 0 * a = 0 := by
  calc
    0 * a = sorry := by sorry
    _ = 0 := by sorry

/-
In the proof below, we use the `suffices` tactic. We start by assuming
`h : (-a) * b + (a * b) = 0` and try to prove the result on this assumption.
Haing done this, it remains to prove `h`.
-/

lemma neg_mul : (-a) * b = -(a * b) := by
  suffices h : (-a) * b + (a * b) = 0 by
    calc (-a) * b = (-a) * b + 0 := by rw [add_zero]
    _ = -(a * b) := by sorry
  calc (-a) * b + (a * b) = sorry := by sorry
    _ = 0 := by sorry

lemma mul_neg : a * (-b) = -(a * b) := by
  calc
    a * (-b) = (-b) * a := by rw [mul_comm]
    _ = -(a * b) := by sorry

lemma neg_neg : -(-a) = a := by
  calc
    -(-a) = -(-a) + 0 := by rw [add_zero]
    _ = a := by sorry

/-
I'm leaving it to you to construct the necessary `calc` structure below.
-/

lemma neg_mul_neg : (-a) * (-b) = a * b := by
  sorry

lemma neg_eq_neg_one_mul : -a = (-1) * a := by
  sorry

end examples
