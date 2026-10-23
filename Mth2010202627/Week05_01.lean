/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Centralisers, conjugacy classes and the class equation

This activity accompanies Chapter 4, "The Class Equation".
Work through the examples in order, replacing each `sorry` with a proof.
Write down the mathematical argument before trying to formalise it.

We first prove some facts for an arbitrary group, then compute in the symmetry
group of a square. The final questions connect these computations to the class
equation and its consequences.

Useful notation: type `\-1` for `⁻¹`, `\in` for `∈`, and `\forall` for `∀`.
In Lean the identity of a multiplicative group is written `1`.
-/

namespace Mth2010202627.Week05_01

variable {G : Type*} [Group G]

/-!
## 1. Fixed by conjugation means commuting

An element `g` acts on `a` by conjugation, sending it to `g * a * g⁻¹`.
Being fixed by this conjugation is equivalent to commuting with `g`.

### Exercise 1

Complete both directions. For the first direction, the `calc` block multiplies
the hypothesis on the right by `g`. Use `simp [mul_assoc]` for the first step
and `rw [h]` for the second. For the reverse direction, rewrite using `h`,
then simplify using associativity.
-/

lemma conjugate_eq_self_iff (g a : G) : g * a * g⁻¹ = a ↔ g * a = a * g := by
  constructor
  · intro h
    calc
      g * a = (g * a * g⁻¹) * g := by sorry
      _ = a * g := by sorry
  · intro h
    sorry

/-!
## 2. The centraliser is a subgroup

The centraliser of `a` consists of the elements `g` satisfying `g * a = a * g`.
As in Week 4, we construct a subgroup by specifying its underlying set and
proving closure under the group operations.

### Exercise 2

The identity proof is supplied. Complete the multiplication and inverse proofs.
For multiplication, move `a` past `h`, then past `g`, using `hh` and `hg`.
For inverses, use the supplied calculation: rewrite `a * g` as `g * a` in
the middle step. The other steps simplify using `simp [mul_assoc]`.
-/

def centralizerSubgroup (a : G) : Subgroup G where
  carrier := {g | g * a = a * g}
  one_mem' := by
    change 1 * a = a * 1
    simp
  mul_mem' := by
    intro g h hg hh
    change g * a = a * g at hg
    change h * a = a * h at hh
    change (g * h) * a = a * (g * h)
    sorry
  inv_mem' := by
    intro g hg
    change g * a = a * g at hg
    change g⁻¹ * a = a * g⁻¹
    calc
      g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by sorry
      _ = g⁻¹ * (g * a) * g⁻¹ := by sorry
      _ = a * g⁻¹ := by sorry

-- Mathlib uses the American spelling `centralizer`, and takes a SET as input.
-- The centraliser of one element is therefore written `Subgroup.centralizer {a}`.
example (a g : G) : g ∈ Subgroup.centralizer {a} ↔ g * a = a * g := by
  exact Subgroup.mem_centralizer_singleton_iff

-- Our construction has the same elements as Mathlib's subgroup.
example (a : G) : centralizerSubgroup a = Subgroup.centralizer {a} := by
  ext g
  exact (Subgroup.mem_centralizer_singleton_iff).symm

/-!
## 3. The centre

Mathlib writes `Subgroup.center G` for the centre `Z(G)`.
The lemma `Subgroup.mem_center_iff` expresses membership as
`∀ g : G, g * z = z * g`. Notice the order of `g` and `z` here.

### Exercise 3. The centre lies in every centraliser

An element commuting with every element of `G` commutes with `a` in particular.
Use `rw [Subgroup.mem_center_iff] at hz`, then specialise `hz` to `a`.
You will need to reverse the resulting equality using `.symm`.
-/

lemma centre_le_centralizer (a : G) : Subgroup.center G ≤ centralizerSubgroup a := by
  intro z hz
  change z * a = a * z
  sorry

/-!
### Exercise 4. Conjugation fixes the centre

Use `conjugate_eq_self_iff` and `Subgroup.mem_center_iff` to prove that an
element belongs to the centre precisely when every conjugation fixes it.
For the reverse direction, start with `rw [Subgroup.mem_center_iff]`, then
`intro g`. The notation `h.mp` uses the forward direction of an equivalence;
`h.mpr` uses the reverse direction.
-/

lemma mem_centre_iff_conjugates_fixed (a : G) :
    a ∈ Subgroup.center G ↔ ∀ g : G, g * a * g⁻¹ = a := by
  constructor
  · intro ha g
    apply (conjugate_eq_self_iff g a).mpr
    sorry
  · intro ha
    sorry

/-!
## 4. Singleton conjugacy classes

The conjugacy class of `a` is the set of all `g * a * g⁻¹` as `g` varies.
The definition below writes membership using an existential quantifier.
It works even when `G` is infinite.
-/

def conjugacySet (a : G) : Set G := {b | ∃ g : G, g * a * g⁻¹ = b}

/-- A worked example: every element belongs to its own conjugacy class. -/
lemma mem_conjugacySet (a : G) : a ∈ conjugacySet a := by
  change ∃ g : G, g * a * g⁻¹ = a
  exact ⟨1, by simp⟩

/-!
### Exercise 5. The singleton classes are exactly the central elements

The proof is started for you. In the forward direction, `hg` proves that
`g * a * g⁻¹` belongs to the conjugacy class. Rewrite its membership using `h`,
then use `Set.mem_singleton_iff`.

In the reverse direction, the previous exercise identifies every conjugate
of `a` with `a`. The identity conjugation witnesses membership of `a` itself.
-/

lemma conjugacySet_eq_singleton_iff (a : G) :
    conjugacySet a = {a} ↔ a ∈ Subgroup.center G := by
  constructor
  · intro h
    apply (mem_centre_iff_conjugates_fixed a).mpr
    intro g
    have hg : g * a * g⁻¹ ∈ conjugacySet a := ⟨g, rfl⟩
    sorry
  · intro ha
    ext b
    constructor
    · rintro ⟨g, rfl⟩
      change g * a * g⁻¹ = a
      sorry
    · intro hb
      have hb' : b = a := Set.mem_singleton_iff.mp hb
      rw [hb']
      exact mem_conjugacySet a

/-!
## 5. Computing in a finite group

The following helper functions enumerate conjugacy classes, centralisers and
the centre. They are supplied; you need not understand their implementation.
Unlike `Set`, `Finset` represents a finite set whose elements we can compute.
`Finset.univ` contains every element, `image` applies a function and removes
duplicates, and `filter` keeps the elements satisfying a condition.
-/

section FiniteComputations

variable [Fintype G] [DecidableEq G]

def conjugacyClassFinset (a : G) : Finset G :=
  Finset.univ.image (fun g => g * a * g⁻¹)

def centralizerFinset (a : G) : Finset G :=
  Finset.univ.filter (fun g => g * a = a * g)

def centreFinset (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Finset G :=
  Finset.univ.filter (fun z => ∀ g : G, g * z = z * g)

/-- Enumerate the DISTINCT conjugacy classes, counting each class only once. -/
def conjugacyClassesFinset (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Finset (Finset G) :=
  Finset.univ.image (fun a : G => conjugacyClassFinset a)

end FiniteComputations

/-!
### The symmetries of a square

Our notes call this group `D₈`, because it has eight elements. Mathlib calls
it `DihedralGroup 4`, where `4` is the number of vertices of the polygon.
The element `DihedralGroup.r i` means `rⁱ`, and `DihedralGroup.sr i` means `s rⁱ`.
Exponents belong to `ZMod 4`, so they are read modulo 4.

The display function labels elements for use with `#eval`.
-/

abbrev D8 := DihedralGroup 4

def rotation : D8 := DihedralGroup.r 1
def reflection : D8 := DihedralGroup.sr 0

def labelD8 : D8 → String
  | .r i => s!"r^{i.val}"
  | .sr i => s!"s r^{i.val}"

#eval Fintype.card D8
#eval (conjugacyClassFinset rotation).image labelD8
#eval (centralizerFinset rotation).image labelD8

/-!
### Exercise 6. Find the classes and centralisers

Before evaluating, predict the conjugacy classes of `1`, `rotation ^ 2`,
`reflection` and `reflection * rotation`. Add `#eval` lines to check.
Also compute `centreFinset D8` and the sizes of the centralisers of these elements.

Check the following claims using `decide`. This tactic proves finite,
decidable statements by computation. Give a group-theoretic explanation on paper
as well: why is the half-turn central, whereas a quarter-turn is not?
-/

example : centreFinset D8 = {1, rotation ^ 2} := by
  sorry

example : conjugacyClassFinset reflection = {reflection, reflection * rotation ^ 2} := by
  sorry

example : (conjugacyClassFinset rotation).card * (centralizerFinset rotation).card =
    Fintype.card D8 := by
  sorry

/-!
## 6. The class equation

Orbit-stabiliser for conjugation gives `|cl(a)| * |C_G(a)| = |G|`.
The DISTINCT conjugacy classes partition `G`, so their sizes sum to `|G|`.
Exercise 5 identifies the singleton classes with the elements of the centre.
Separating those classes gives the class equation

`|G| = |Z(G)| + ∑ |cl(aᵢ)|`,

where the sum has ONE representative for each noncentral conjugacy class.
For `D₈`, the classes have sizes `1, 1, 2, 2, 2`.

### Exercise 7

1. Evaluate `(conjugacyClassesFinset D8).image (fun c => c.image labelD8)`.
   Check that the proposed representatives below account for every class.
2. Complete the proofs using `decide`.
3. Write the class equation both as a sum of class sizes and as a sum of
   centraliser indices. What goes wrong if you sum over every group element
   instead of choosing one representative from each class?
-/

example : conjugacyClassesFinset D8 =
    {conjugacyClassFinset (1 : D8), conjugacyClassFinset (rotation ^ 2),
      conjugacyClassFinset rotation, conjugacyClassFinset reflection,
      conjugacyClassFinset (reflection * rotation)} := by
  sorry

example : Fintype.card D8 = (centreFinset D8).card +
    (conjugacyClassFinset rotation).card +
    (conjugacyClassFinset reflection).card +
    (conjugacyClassFinset (reflection * rotation)).card := by
  sorry

/-!
### Further questions (on paper)

* Repeat the computations for `DihedralGroup 3` and `DihedralGroup 5`.
  How does the centre differ from that of `D₈`? Form a conjecture about the
  centre of `DihedralGroup n` for odd `n ≥ 3`.
* Suppose `|G| = pˢ`, where `p` is prime and `s ≥ 1`. Each noncentral class
  has size greater than 1 and dividing `pˢ`. Why is each size divisible by `p`?
  Use the class equation to show that `p` divides `|Z(G)|`, and hence that
  the centre has more than one element. Where do you use `1 ∈ Z(G)`?
* A normal subgroup is a union of whole conjugacy classes and contains `1`.
  In `A₅`, the class sizes are `1, 15, 20, 12, 12`. Combine this with Lagrange's
  theorem to show that the only possible orders of a normal subgroup are 1 and 60.
-/

end Mth2010202627.Week05_01
