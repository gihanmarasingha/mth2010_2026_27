import Mathlib

variable {R} [CommRing R]

variable (I J : Ideal R)

/-
# Sums and products of ideals

Our goal is to prove that if `I` and `J` are ideals of a ring `R`, then so are
`I + J` and `I * J`.

Here,

  `I + J = {a + b | a ∈ I and b ∈ J}`

and

  `I * J = {∑ᵢ aᵢ * bᵢ : aᵢ ∈ I and bᵢ ∈ J}`

where the sum is over a finite set.
-/

/-
## Using ideal properties

Here are the three main properties that define an ideal and how to use them.
-/

example : 0 ∈ I := by apply zero_mem

example {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by apply add_mem hx hy

example {x r : R} (hx : x ∈ I) : r * x ∈ I := by apply Ideal.mul_mem_left _ _ hx

/-
Remember you can use `ring` to prove equations involving a ring.
-/

example (a b r : R) : r * (a + b) = r * a + r * b := by ring

/-
## Sum of ideals

The carrier of the sum of `I` and `J` is the set

  `{x | ∃ a ∈ I, ∃ b ∈ J, x = a + b}`

of elements of `R`.

It remains to show this set contains `0` and is closed under addition and
under multiplication on the left by elements of `R`.
-/

@[simp]
def sum_set : Set R :=  {x | ∃ a ∈ I, ∃ b ∈ J, x = a + b}

namespace principal_example

open Submodule

/-
## A sum set example

Below, we define the principal ideals `I₁ = (2)` and `I₂ = (3)` of `ℤ`. One
can see that `1 ∈ I₁ + I₂` as `1 = 2 * 2 + 3 * (-1)`.
-/

def I₁ : Ideal ℤ := span ℤ {2}

def I₂ : Ideal ℤ := span ℤ {3}

lemma one_in_I_sum : 1 ∈ sum_set I₁ I₂ := by
  dsimp [sum_set]
  use 4, ?_, (-3), ?_ -- remains to show `1 = 4 - 3`, `4 ∈ I₁` and `-3 ∈ I₂`
  · show 1 = 4 + -3; simp
  · show 4 ∈ I₁
    simp [I₁]
    rw [Ideal.mem_span_singleton]
    norm_num
  show -3 ∈ I₂
  simp [I₂]
  rw [Ideal.mem_span_singleton]

/-
### Exercise

Adapt the above to show that `1 ∈ J₁ + J₂`, where `J₁ = (5)` and `J₂ = (7)`.
-/

def J₁ : Ideal ℤ := span ℤ {5}

def J₂ : Ideal ℤ := span ℤ {7}

example : 1 ∈ sum_set J₁ J₂ := by
  sorry

/-
### (Optional) Exercise

Show that the univeral set of `ℤ` equals `sum_set I₁ I₂` by completing the
following.
-/

example : Set.univ = sum_set I₁ I₂ := by
  apply le_antisymm
  · rintro a -
    simp [sum_set]
    use 4 * a, ?_, (-3) * a, ?_
    · ring
    · simp [I₁]
      rw [Ideal.mem_span_singleton]
      use 2 * a
      ring
    simp [I₂]
    rw [Ideal.mem_span_singleton]
    simp
  rintro a -
  simp

end principal_example

def sum_ideal : Ideal R where
  carrier := sum_set I J
  add_mem' := by
    show ∀ x₁ x₂, x₁ ∈ sum_set I J → x₂ ∈ sum_set I J → x₁ + x₂ ∈ sum_set I J
    intro x₁ x₂ hx₁' hx₂'
    -- Here `hx₁' : x₁ ∈ sum_set I J` and `hx₂' : x₂ ∈ sum_set I J`.
    rcases hx₁' with ⟨
      a₁ : R,
      ha₁ : a₁ ∈ I,
      b₁ : R,
      hb₁ : b₁ ∈ J,
      hx₁ : x₁ = a₁ + b₁
    ⟩
    rcases hx₂' with ⟨a₂, ha₂, b₂, hb₂, hx₂⟩
    show x₁ + x₂ ∈ sum_set I J
    use a₁ + a₂
    constructor
    · show a₁ + a₂ ∈ I
      apply add_mem ha₁ ha₂
    use b₁ + b₂
    constructor
    · show b₁ + b₂ ∈ J
      apply add_mem hb₁ hb₂
    rw [hx₁, hx₂]
    ring
  zero_mem' := by
    show 0 ∈ sum_set I J
    show ∃ a ∈ I, ∃ b ∈ J, 0 = a + b
    use 0
    constructor
    · show 0 ∈ I; simp
    use 0
    constructor
    · show 0 ∈ J; simp
    show 0 = 0 + 0; simp
  smul_mem' := by
    show ∀ r x, x ∈ sum_set I J → r * x ∈ sum_set I J
    rintro r x hx'
    rcases hx' with ⟨a, ha, b, hb, hx⟩
    show r * x ∈ sum_set I J
    rw [hx]
    use r * a
    constructor
    · show r * a ∈ I
      apply Ideal.mul_mem_left _ _ ha
    use r * b
    constructor
    · show r * b ∈ J
      apply Ideal.mul_mem_left _ _ hb
    show r * (a + b) = r * a + r * b
    ring

/-
### (Optional) Exercise

Prove the following result that if an ideal `I` contains `1`, then it is the
whole ring `R`. In Mathlib, this ideal is denoted `⊤`.
-/

lemma eq_univ_of_one_mem (h : 1 ∈ I) : ⊤ = I := by
  apply le_antisymm
  · rintro a -
    simpa using Ideal.mul_mem_left I a h
  rintro a -
  simp

/-
## Products of ideals

In the definition below, the product set is the set of all `x : R` of the form

  `x = ∑ i, a i * b i `

This is a sum over all `i : ι` of `(a i) * (b i)`. Here, the functions
`a : ι → R` and `b : ι → R` are sequences of elements of `R`
with the condition that `a i ∈ I` and `b i ∈ J`.

The sum is indexed over the type `i`, which is finite.
-/

@[simp]
def prod_set : Set R :=
  {x | ∃ (ι : Type*) (_ : Fintype ι)
        (a b : ι → R),
        (∀ i, a i ∈ I ∧ b i ∈ J) ∧
        x = ∑ i, a i * b i }

/-
### Product with 0

As a first example, let `I` be an ideal of `R`. Consider the product `I * 0`.
-/

/--
As sets, `0 * I ⊆ {0}`.
-/
lemma prod_set_zero_sub_zero : prod_set 0 I ⊆ {0} := by
  intro z hz
  rcases hz with ⟨ι, hι, a, b, h, hz⟩
  simp
  show z = 0
  have : ∀ i : ι, a i = 0 := by
    intro i
    apply (h i).1
  simpa [this] using hz

/--
As sets, `{0} ⊆ 0 * I`
-/
lemma zero_sub_prod_set_zero : {0} ⊆ prod_set 0 I := by
  simp
  use PUnit, inferInstance
  let a : PUnit → R := fun i => 0
  let b : PUnit → R := fun i => 0
  use a, b
  constructor
  all_goals simp[a, b]

/--
As sets, `{0} = 0 * I`
-/
lemma prod_set_zero_eq_zero : prod_set 0 I = {0} := by
  apply subset_antisymm
  · apply prod_set_zero_sub_zero
  apply zero_sub_prod_set_zero

/-
### Exercise

As before, we need to show that the set `prod_ideal I₁ I₂` is an ideal of `R`.
This is considerably harder than the same task for `sum_set` and `sum_ideal` as
we need to work with indexed sums. For `add_mem'`, we need to understand
so-called `Sum` types.
-/

def prod_ideal : Ideal R where
  carrier := prod_set I J
  add_mem' := by
    intro x₁ x₂ hx₁' hx₂'
    rcases hx₁' with ⟨ι₁, _, a₁, b₁, h₁, hx₁⟩
    rcases hx₂' with ⟨ι₂, _, a₂, b₂, h₂, hx₂⟩
    use ι₁ ⊕ ι₂, inferInstance
    use fun i =>
        match i with
        | Sum.inl i₁ => a₁ i₁
        | Sum.inr i₂ => a₂ i₂
    use fun i =>
        match i with
        | Sum.inl i₁ => b₁ i₁
        | Sum.inr i₂ => b₂ i₂
    constructor
    · intro i
      constructor
      · match i with
        | Sum.inl i₁ =>
          simp
          apply (h₁ i₁).1
        | Sum.inr i₂ =>
          simp
          apply (h₂ i₂).1
      match i with
      | Sum.inl i₁ =>
          simp
          apply (h₁ i₁).2
      | Sum.inr i₂ =>
          simp
          apply (h₂ i₂).2
    simp [hx₁, hx₂]
  zero_mem' := by
    use PUnit, inferInstance
    use fun i => 0
    use fun i => 0
    constructor
    · simp
    simp
  smul_mem' := by
    intro r x hx'
    rcases hx' with ⟨ι, hι, a, b, h, hx⟩
    use ι, hι
    use fun i => r * (a i)
    use b
    constructor
    · intro i
      constructor
      · have ha : a i ∈ I := (h i).1
        apply Ideal.mul_mem_left _ _ ha
      have hb : b i ∈ J := (h i).2
      exact hb
    rw [hx]
    calc r * ∑ i, a i * b i = ∑ i, r * (a i * b i) := by simp [Finset.mul_sum]
      _ = ∑ i, (r * a i) * b i := by simp [mul_assoc]

namespace principal_example

/-
### (Hard) Exercises

Recall our earlier example where `I₁ = (2)` and `I₂ = (3)` are principal ideals
of `ℤ`.

Your task now is to prove `I₁ I₂ = (6)`. This can be decomposed into smaller
tasks.

### (Hard) Exercise

Your first smaller task is to show `I₁ I₂ ⊆ (6)` as sets. Using this, you can
show `I₁ I₂ ⊆ (6)` as ideals. Mathlib uses the notation `≤` for inclusion of
ideals.
-/

open Submodule

lemma example_prod_set_sub_principal : prod_set I₁ I₂ ⊆ {6 * r | r : ℤ} := by
  intro x hx
  rcases hx with ⟨ι, _, a, b, h, hx⟩
  simp
  rw [hx]
  simp [I₁, I₂] at h
  simp [Ideal.mem_span_singleton] at h
  let c : ι → ℤ := fun i => Classical.choose (h i).1
  let d : ι → ℤ := fun i => Classical.choose (h i).2
  have hc : ∀ i, a i = 2 * (c i) := fun i => Classical.choose_spec (h i).1
  have hd : ∀ i, b i = 3 * (d i) := fun i => Classical.choose_spec (h i).2
  have hab : ∀ (i : ι), a i * b i = 6 * (c i * d i) := by
    intro i
    rw [hc i, hd i]
    ring
  simp [hab, ←Finset.mul_sum]

lemma example_prod_ideal_le_principal : prod_ideal I₁ I₂ ≤ span ℤ {6} := by
  intro x hx
  simp
  rw [Ideal.mem_span_singleton]
  obtain ⟨r, hr⟩ := example_prod_set_sub_principal hx
  use r
  simp [hr]

/-
### (Hard) Exercise

Now we prove the converse, that `(6) ⊆ prod_set I₁ I₂` and that
`(6) ≤ prod_ideal I₁ I₂`.
-/

lemma example_principal_sub_prod_set : {6 * r | r : ℤ} ⊆ prod_set I₁ I₂ := by
  intro z hz
  rcases hz with ⟨x, hx⟩
  dsimp [prod_set]
  use PUnit, inferInstance
  let a : PUnit → ℤ := fun i => 2
  let b : PUnit → ℤ := fun i => 3 * x
  use a, b
  constructor
  · intro i
    simp [I₁, I₂, Ideal.mem_span_singleton, a, b]
  simp [a, b, ←hx]
  ring

lemma example_principal_le_prod_ideal : span ℤ {6} ≤ prod_ideal I₁ I₂ := by
  simp
  intro z hz
  rw [Ideal.mem_span_singleton] at hz
  rcases hz with ⟨r, hr⟩
  apply example_principal_sub_prod_set
  use r
  simp [hr]

/-
### Exercise

Using the above, we show the sets (respectively ideals) are equal.
-/

lemma example_principal_eq_prod_set : {6 * r | r : ℤ} = prod_set I₁ I₂ := by
  apply subset_antisymm
  · apply example_principal_sub_prod_set
  apply example_prod_set_sub_principal

lemma example_principal_eq_prod_ideal : span ℤ {6} = prod_ideal I₁ I₂ := by
  apply le_antisymm
  · apply example_principal_le_prod_ideal
  apply example_prod_ideal_le_principal

end principal_example
