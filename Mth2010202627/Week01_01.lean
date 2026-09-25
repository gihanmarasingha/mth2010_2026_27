import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Permutations and cycle notation

In this file (a Lean *module*), we work with permutation groups.

In Mathlib, `Equiv.Perm (Fin n)` is the group of permutations on `{0, 1, ..., n - 1}`.
We abbreviate this to `S n`. It is essentially the same as the standard `Sₙ`.
-/

open Equiv

/-- `S n` is the group of permutations on `{0, 1, 2, ..., n - 1}` -/
abbrev S (n : Nat) := Perm (Fin n)

/-!
## Basic calculations and examples

Below, we work with examples in `S₅`:

`c₁ = (0 1 3), c₂ = (2 4), s = c₁ c₂, t = (0 1 2 3 4)`

A cycle such as `(0 1 3)` is represented in Lean as `c[0, 1, 3]`.

The `#eval` command is used to compute and print permutations as disjoint products of cycles.

Here, `s ^ m` represents the power `sᵐ`.

The syntax of a Lean definition (with no arguments) takes the form

`def t : σ := x`

where `def` is a keyword, `t` is the name of a term of type `σ` and `x` is an expression for `t`.
-/

/-- `c1 = (0 1 3)` -/
def c1 : S 5 := c[0, 1, 3]

/-- `c2 = (2 4)`-/
def c2 : S 5 := c[2, 4]

#eval (c[0, 1, 2] : S 3) * (c[0, 1])


#eval (c[0, 1] : S 3) * (c[0, 1, 2])

/-- `c3 = c1 c2`. Use `*` for multipication in Lean. -/
def s : S 5   := c1 * c2

/-- `t = (0 1 2 3 4)` -/
def t : S 5 := c[0, 1, 2, 3, 4]

#eval s

#eval s ^ 3

#eval t

#eval s * t

#eval t * s

/-!
Type `\-1` to enter `⁻¹`. So `t⁻¹` is the inverse of `t`.
-/

#eval t⁻¹


/-!

### Exercise 1

1. Let `u = (0 1)(3 1), v = (2 4 1)(3 2)`. By hand, express each of `u`, `v`, `u v`, `v u`,
  `v³`, and `u⁻¹` as products of disjoint cycles.

2. Below, replace `sorry` in each line with appropriate products of cycles to give Lean definitions
  of `u` and `v` from the question above.

3. Then use `#eval` to compute each of of the quantities from Question 1 of this exercise. Remember
  to write `v³` as `v ^ 3`.

3. Evaluate `u ^ m` for different values of the natural number `m`. What do you observe?
-/

/-- `u = (0 1)(3 1)` -/
def u : S 5 := sorry

/-- `v = (2 4 1)(3 2)` -/
def v : S 5 := sorry

/-!

### Simple proofs of equality and inequality

Our first proof is

`example : s * t ≠ t * s := by decide`

Here, `s * t ≠ t * s` is the statement to be proved. The proof itself is `by decide`. This
tells Lean to look for and use any appropriate decision procedure.

This works (sometimes) in finite concrete examples.
 -/

example : s * t ≠ t * s := by decide

example : s * t = c[1, 4] * c[3, 2, 0] := by decide

example : s⁻¹⁻¹ = s := by decide


/-!

## Order of an element

For a finite group `G`, the order of a group element `g ∈ G` is the smallest positive integer `n`
such that `gⁿ = 1` (where `1` is the identity element, usally written `e` in standard mathmematics).

The following Lean code computes the order of any group element. You need not understand the code.
-/

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def OrderOf(g : G) : ℕ :=
  let L := (List.range (Fintype.card G + 1)).filter (fun n => 0 < n ∧ g ^ n = 1)
  L.headD 1

/-!

### Playing with orders.

Let's investigate the orders of some elements.

-/

#eval OrderOf c1

#eval OrderOf c2

#eval OrderOf (c1 * c2)

#eval OrderOf (s * t)



/-!

### Exercise 2

* Find an element of `S 5` of order `6`.
* Find an element of `S 7` of order `6`, expressed as a product of 3 disjoint
  cycles (not including singleton cycles).
* Check your answers in the space below by defining cycles in Lean and using
  `OrderOf`
-/












/-!

## The sign of a permutation

A permutation is of odd sign (or has sign -1) if it can be expressed as a product of an odd
number of transpositions. Otherwise, it is even (or has sign 1)
-/

#eval c1.sign

#eval c2.sign

#eval (c1 * c2).sign




/-!

### Exercise 3

1. How does the sign depend on the cycle type of a permutation?
2. Check this by calculation in Lean in the space below.
-/








/-!

## Group actions

Let `G` be a group and let `M` be a set. A group action is a function
`G × M → M`. Given `g ∈ G` and `m ∈ M`, we write `g • m` for the value of this
function on the tuple `(g, m)`. To be a group action, the function must satisfy

1. `1 • b = b` for all `b ∈ M.
2.  `(x * y) • b = x • y • b`, for all `x, y ∈ G`, for all `b ∈ M`.


### The conjugacy action

A group `G` acts on itself by the conjugacy action

`g • h := g * h * g⁻¹`

### Exercise 4

1. Show, by hand, that the conjugacy action is a group action.
2. Complete the Lean proof below that the conjugacy action is a group action.

-/


variable {G : Type*} [Group G] {M : Type*}  [MulAction G M]

def conjMulAction : MulAction G G where
  smul := fun g h => g * h * g⁻¹
  one_smul := by
    intro h
    change 1 * h * 1⁻¹ = h
    group
  mul_smul := by
    intro x y b
    sorry


/-!

## Commutators

Mathlib defines the commutator `⁅s, t⁆ = s * t * s⁻¹ * t⁻¹`.

Type `\[--` to produce the commutator brackets.
-/

#eval ⁅s, t⁆

#eval ⁅s, s⁆

#eval s

/-!

### Exercise 5

1. Experiment, by varying `x`, to determine when `⁅s, x⁆` is `1` (Don't skip
  past the following blank lines that contain the answer)!

2. Can you generalise your observation?

3. Prove your result by hand.

4. Now skip past the following blank lines and complete the Lean proof.
-/




















example {n : Nat} (a b : S n) : a * b = b * a ↔ ⁅a, b⁆ = 1 := by
  constructor -- This creates two goals: one for each direction of ↔
  · -- This goal is to prove `a * b = b * a → ⁅a, b⁆ = 1`
    intro (h : a * b = b * a)
    show a * b * a⁻¹ * b⁻¹ = 1
    rw [h]
    show b * a * a⁻¹ * b⁻¹ = 1
    group
  · -- This goal is to prove `⁅a, b⁆ = 1 → a * b = b * a`
    intro (h : ⁅a, b⁆ = 1)
    change a * b * a⁻¹ * b⁻¹ = 1 at h
    show a * b = b * a
    calc a * b = a * b * a⁻¹ * b⁻¹ * b * a  := by sorry
    _ = 1 * b * a                           := by sorry
    _ = b * a                               := by sorry


/-- The centralizer of `s` as a finset. -/
def centralizerSet {n : Nat} (s : Perm (Fin n)) : Finset (Perm (Fin n)) :=
  (Finset.univ : Finset (Perm (Fin n))).filter (fun t => s * t = t * s)

#eval centralizerSet s


/-!
### Exercise 6

1. What do you notice about the elements of `centralizer s`?
2. Make a conjecture regarding what `centralizer x` looks like. Try different
  values of `x` to test your conjecture.
3. Prove your conjecture, by hand.


-/

/-- The set of all powers `c₁ᵃ c₂ᵇ` -/
def expected : Finset (Perm (Fin 5)) :=
  let as := List.range 3   -- a = 0,1,2
  let bs := List.range 2   -- b = 0,1
  let lst : List (Perm (Fin 5)) :=
    as >>= fun a => bs.map (fun b => c1 ^ a * c2 ^ b)
  lst.toFinset

#eval s                        -- prints: c[0, 1, 3] * c[2, 4]
#eval (centralizerSet s).card         -- expect 6
#eval expected.card            -- = 6
#eval decide (expected = centralizerSet s)  -- expect `true`


#min_imports
#redundant_imports
