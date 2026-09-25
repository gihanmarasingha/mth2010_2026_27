import Mathlib

namespace Mth2010202627.Week07_01

/-
# Permutation representations
-/

/-
## Recap of group actions
Let `(G, *)` be a group and `A` a set (or type in Lean). We denote by
`• : G × A → A` a group action satisfying the properties

* `1 • a = a` for all `a ∈ A` and
* `(g₁ * g₂) • a = g₁ • (g₂ • a)` for all `g₁, g₂ ∈ G` and `a ∈ A`.



**Notes**

* `•` is not a group operation! The set `A` need not be a group.
* The symbol `•` is typed as `\bu` or `\smul`.

The equations that define a group action are represented in Lean as follows:
-/

variable {G A : Type*} [Group G] [MulAction G A]

-- A proof that `1 • a = a`
example (a : A) : (1 : G) • a = a := by
  simp

-- A proof that `(g₁ * g₂) • a = g₁ • (g₂ • a)`
example (g₁ g₂ : G) (a : A) : (g₁ * g₂) • a = g₁ • (g₂ • a) := by
  rw [mul_smul]

/-
# Permutations from Group Actions

We define `τₕ : A → A` by `τₕ(a) = h • a`
-/

def τ (g : G) : A → A := fun a => g • a

/-
Then `τₕ` is a bijection for each `h ∈ G`.

One way to prove this is to define a function `σₕ` , for each `h ∈ G`, and show that
`σₕ` is a left inverse of `τₕ` and that `σₕ` is a right inverse of `τₕ`.

Remember that if `p : X → Y` and `q : Y → X`, then

* `p` is a left inverse of `q` means `p (q y) = y` for all `y ∈ Y`.
* `p` is a right inverse of `q` means `q (p x) = x` for all `x ∈ X`.
-/

open Function

/-
Define `σ` so that for every `g ∈ G` we have that for every `a ∈ A`,
  `(σ g) (τ g a) = a` and `(τ g) (σ g a) = a`.
-/

def σ (g : G) : A → A := τ g⁻¹


lemma left_inverse (g : G) : LeftInverse (σ g) (τ g : A → A) := by
  dsimp [LeftInverse]
  sorry

lemma right_inverse (g : G) : RightInverse (σ g) (τ g : A → A) := by
  dsimp [RightInverse]
  sorry

/-
Go to leansearch.net to find a result that states `f` is bijective
if and only if `f` has a left inverse and a right inverse. Then complete
the proof below.
-/

lemma tau_bijective (g : G) : Bijective (τ g : A → A) := by
  sorry

/-
The permutation representation is the map `π : G → Symm(A)` (where Symm(A) is the symmetry
group of `A`) given by `π(h) = τₕ`.

In Lean, we write `Equiv.Perm A` for `Symm(A)`.

Note that to specify an element of `Equiv.Perm A` is to specify a function
`toFun : A → A`, specify an inverse `invFun : A → A` and give proofs `left_inv` and
`right_inv`.
-/

/-
## The permutation representation
-/

def π (g : G) : Equiv.Perm A where
  toFun := τ g
  invFun := sorry
  left_inv := by
    unfold LeftInverse
    sorry
  right_inv := by
    unfold RightInverse
    sorry

/-
## The permutation representation as a group homomorphism

To show the permtuation representation is a homomorphism in Lean, we must show

* `π 1 = 1` and
* `π (x * y) = π x * π y` for all `x, y ∈ G`

Note in ordinary mathematics, we get `π 1 = 1` for free.
-/

def permRep : G →* Equiv.Perm A :=
{ toFun    := π,
  map_one' := by
    ext a
    sorry
  map_mul' := by
    sorry }

end Mth2010202627.Week07_01
