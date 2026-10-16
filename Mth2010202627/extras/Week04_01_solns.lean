/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Group homomorphisms — solutions

We construct homomorphisms, then prove that their images and kernels are subgroups.
These are completed solutions to the exercises in `../Week04_01.lean`.
The exercise statements and hints are retained for reference.

Useful notation: type `\to*` for `→*`, `\to+` for `→+`, and `\-1` for `⁻¹`.
-/

namespace Mth2010202627.Week04_01.Solutions

/-!
## 1. Constructing multiplicative homomorphisms

For groups written multiplicatively, `G →* H` is Lean's type of group homomorphisms.
Its name in Mathlib is `MonoidHom`: the same structure also works for monoids.
To construct one, supply three fields:

* `toFun`: the underlying function;
* `map_one'`: a proof that the identity maps to the identity;
* `map_mul'`: a proof that products are preserved.

For groups, preserving the identity follows from preserving products, but this
structure asks us to supply both proofs. In Lean the identity is written `1`.
-/

variable {G H : Type*} [Group G] [Group H]

/-- A worked example: the identity homomorphism on any group. -/
def identityHom (G : Type*) [Group G] : G →* G where
  toFun := fun x => x
  map_one' := by rfl
  map_mul' := by
    intro x y
    rfl

-- A homomorphism can be applied to an element just like an ordinary function.
example (x : G) : identityHom G x = x := by rfl

/-!
### Exercise 1. The trivial homomorphism

Construct the map sending every element of `G` to `1 : H`.
For `map_mul'`, use `intro x y`, then `simp`.
-/

def trivialHom (G H : Type*) [Group G] [Group H] : G →* H where
  toFun := fun _ => 1
  map_one' := by
    rfl
  map_mul' := by
    intro x y
    simp

/-!
### Exercise 2. Projection from a product

The product group has componentwise multiplication:
`(g₁, h₁) * (g₂, h₂) = (g₁ * g₂, h₁ * h₂)`.
Construct the first projection `(g, h) ↦ g`. Access the components of `p` using
`p.1` and `p.2`. Both proof fields can be completed using `rfl` (after `intro`
where necessary).
-/

def firstProjection (G H : Type*) [Group G] [Group H] : G × H →* G where
  toFun := fun p => p.1
  map_one' := by
    rfl
  map_mul' := by
    intro p q
    rfl

-- This is a concrete homomorphism even when the groups are noncommutative.
example : firstProjection G H (1, 1) = 1 := by
  exact (firstProjection G H).map_one

/-!
## 2. Concrete additive examples

The integers form a group under **addition**, so use `ℤ →+ ℤ`, not `ℤ →* ℤ`.
An additive homomorphism has fields `toFun`, `map_zero'`, and `map_add'`.
In an additive group, the identity is `0` and the inverse of `x` is `-x`.

### Exercise 3. Doubling integers

Construct the additive homomorphism `n ↦ 2 * n`.
The zero proof is supplied. For the addition proof, try `ring` after `intro m n`.
Why does this formula fail to preserve multiplication on integers?
-/

def doubleHom : ℤ →+ ℤ where
  toFun := fun n => 2 * n
  map_zero' := by simp
  map_add' := by
    intro m n
    change 2 * (m + n) = 2 * m + 2 * n
    ring

#eval doubleHom 7      -- 14
#eval doubleHom (-3)   -- -6

/-!
### Exercise 4. Reduction modulo 3

`ZMod 3` is the group of integers modulo 3, written additively.
The expression `(n : ZMod 3)` is the residue class of the integer `n`.
Complete the proofs using `simp` (and `intro m n` for the addition proof).
-/

def modThreeHom : ℤ →+ ZMod 3 where
  toFun := fun n => (n : ZMod 3)
  map_zero' := by
    simp
  map_add' := by
    intro m n
    simp

#eval modThreeHom 7    -- 1
#eval modThreeHom 9    -- 0
#eval modThreeHom (-1) -- 2

/-!
## 3. Homomorphisms preserve inverses

For `f : G →* H`, Mathlib provides `f.map_one` and `f.map_mul x y`.
We first use these to prove that `f (x⁻¹) = (f x)⁻¹` ourselves.

### Exercise 5

The lemma `eq_inv_of_mul_eq_one_left` says that `a * b = 1` implies `a = b⁻¹`.
After applying it, the goal is `f (x⁻¹) * f x = 1`.
Finish by rewriting with `← f.map_mul`, `inv_mul_cancel`, and `f.map_one`.
For this exercise, do not use Mathlib's already-proved lemma `map_inv`.
-/

lemma hom_map_inv (f : G →* H) (x : G) : f (x⁻¹) = (f x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← f.map_mul, inv_mul_cancel, f.map_one]

/-!
## 4. The image is a subgroup

The image of `f : G →* H` is `{y : H | ∃ x : G, f x = y}`.
To construct a `Subgroup H`, give its underlying set (`carrier`) and proofs that
it contains `1` and is closed under multiplication and inverses.

The notation `⟨x, hx⟩` supplies a witness `x` and a proof `hx` for an existential.
Conversely, `rcases hy with ⟨x, hx⟩` extracts them from an existential hypothesis.

### Exercise 6

The identity proof is supplied. Complete the two closure proofs.

* For multiplication, extract preimages `a` of `y` and `b` of `z`.
  Use `a * b` as a preimage of `y * z`.
* For inverses, extract a preimage `a` of `y` and use `a⁻¹`.
  Use `hom_map_inv` from Exercise 5.

Here, `change` expresses a membership goal in terms of the defining set.
We construct the subgroup directly, without using Mathlib's `f.range`.
-/

def imageSubgroup (f : G →* H) : Subgroup H where
  carrier := {y | ∃ x, f x = y}
  one_mem' := by
    change ∃ x, f x = 1
    exact ⟨1, f.map_one⟩
  mul_mem' := by
    intro y z hy hz
    change ∃ x, f x = y at hy
    change ∃ x, f x = z at hz
    rcases hy with ⟨a, ha⟩
    rcases hz with ⟨b, hb⟩
    change ∃ x, f x = y * z
    refine ⟨a * b, ?_⟩
    rw [f.map_mul, ha, hb]
  inv_mem' := by
    intro y hy
    change ∃ x, f x = y at hy
    change ∃ x, f x = y⁻¹
    rcases hy with ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    rw [hom_map_inv, ha]

/-!
## 5. The kernel is a subgroup

The kernel of `f : G →* H` is `{x : G | f x = 1}`.
Notice that the image is a subgroup of the **codomain** `H`, whereas the kernel
is a subgroup of the **domain** `G`.

### Exercise 7

Complete the closure proofs. For multiplication, use `f.map_mul`, `hx`, and `hy`.
For inverses, use `hom_map_inv` and `hx`, then simplify `1⁻¹` using `simp`.
Again, construct the subgroup directly, without using Mathlib's `f.ker`.
-/

def kernelSubgroup (f : G →* H) : Subgroup G where
  carrier := {x | f x = 1}
  one_mem' := by
    exact f.map_one
  mul_mem' := by
    intro x y hx hy
    change f x = 1 at hx
    change f y = 1 at hy
    change f (x * y) = 1
    rw [f.map_mul, hx, hy, one_mul]
  inv_mem' := by
    intro x hx
    change f x = 1 at hx
    change f (x⁻¹) = 1
    rw [hom_map_inv, hx]
    simp

/-!
### Connecting our constructions to Mathlib

Mathlib calls the image `f.range` and the kernel `f.ker`.
For additive homomorphisms, these are `AddSubgroup`s instead of `Subgroup`s.
The following are worked examples: `rfl` works because the membership conditions
are true by definition. The last two examples identify our subgroups with Mathlib's.
-/

example (f : G →* H) (y : H) : y ∈ f.range ↔ ∃ x, f x = y := by rfl

example (f : G →* H) (x : G) : x ∈ f.ker ↔ f x = 1 := by rfl

example (f : G →* H) : imageSubgroup f = f.range := by
  ext y
  rfl

example (f : G →* H) : kernelSubgroup f = f.ker := by
  ext x
  rfl

/-!
## 6. Identifying images and kernels in examples

### Exercise 8. The first projection

Show that the kernel consists of pairs whose first component is `1`.
Then show that every element of `G` belongs to the image: find a pair mapping to it.
For the second proof, use `change ∃ p : G × H, firstProjection G H p = g`.
-/

example (p : G × H) : p ∈ kernelSubgroup (firstProjection G H) ↔ p.1 = 1 := by
  rfl

example (g : G) : g ∈ imageSubgroup (firstProjection G H) := by
  change ∃ p : G × H, firstProjection G H p = g
  exact ⟨(g, 1), rfl⟩

/-!
### Exercise 9. Doubling and reduction modulo 3

For additive homomorphisms, membership of the kernel means `f x = 0`.
Use `change` to expose this equation, then `decide` for the first two goals.
For the last goal, give a preimage of `8` under `doubleHom`.

On paper, describe the entire image and kernel of each map. Which map is
injective? Which is surjective? Use the evaluations above to guide your answers.
-/

example : (9 : ℤ) ∈ modThreeHom.ker := by
  change (9 : ZMod 3) = 0
  decide

example : (7 : ℤ) ∉ modThreeHom.ker := by
  change ¬ ((7 : ZMod 3) = 0)
  decide

example : (8 : ℤ) ∈ doubleHom.range := by
  change ∃ n : ℤ, doubleHom n = 8
  exact ⟨4, by norm_num [doubleHom]⟩

/-!
### Answers to the paper questions

* Doubling does not preserve multiplication: `2 * (1 * 1) ≠ (2 * 1) * (2 * 1)`.
* The first projection has image all of `G` and kernel `{(1, h) | h ∈ H}`.
* Doubling has image the even integers and kernel `{0}`. It is injective,
  since `2 * m = 2 * n` implies `m = n`, but is not surjective: `1` is not even.
* Reduction modulo 3 has image all of `ZMod 3` and kernel the multiples of 3.
  Each residue class has an integer representative, so the map is surjective.
  It is not injective: `0` and `3` have the same image.
-/

end Mth2010202627.Week04_01.Solutions
