import Mathlib

open Polynomial

set_option linter.unusedTactic false

noncomputable section

def f : ℚ[X] := 3 * X + 1

def g : ℚ[X] := 5 * X^2 + 3

def fs : ℕ →₀ ℚ :=
  Finsupp.single 0 (1)

def ps : Polynomial ℚ := Polynomial.ofFinsupp fs

example : ps = C 1 := by rfl

example : f + g = 5 * X ^ 2 + 3 * X + 4 := by
  simp [f, g]
  ring

example : f * g = (15 * X ^ 3 + 5 * X ^ 2 + 9 * X + 3) := by
  simp [f, g]
  ring

example : f.eval 2 = 7 := by
  simp [f]
  norm_num

example : f.degree = 1 := by
  apply degree_linear -- The result that a linear polynomial has degree 1
  norm_num

example (a : WithBot ℕ) (h : a < 1) : a ≤ 0 := by exact Nat.WithBot.lt_one_iff_le_zero.mp h

example (p : ℚ[X]) (c : ℚ) (hc : p.eval c = 0) : (X - C c) ∣ p := by
  let q := X - C c
  let d := p /ₘ q -- division of by the monic polynomial q
  let r := p %ₘ q -- remainder on dividing p by the monic polynomial q
  have h2 : q.Monic := monic_X_sub_C c -- proof that q is indeed monic
  have h1 : r.degree < q.degree := p.degree_modByMonic_lt h2
  have euclid : r + q * d = p := modByMonic_add_div p h2
  suffices h : r = 0 by
    use d -- We'll show p = q * d
    symm
    simpa [h] using euclid
  have qdeg : q.degree = 1 := degree_X_sub_C c
  rw [qdeg] at h1 -- ⊢ `r = 0`
  have rdeg_le : r.degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp h1
  have req : r = C (r.coeff 0) := r.degree_le_zero_iff.mp rdeg_le
  rw [req] at ⊢ euclid -- `⊢ C (r.coeff 0) = 0`
  have hq : eval c q = 0 := by simp [q, eval_sub, eval_X, eval_C]
  have hcoeff : r.coeff 0 = 0 := by
    have := congrArg (fun s : ℚ[X] => eval c s) euclid
    -- `this` states the evaluation at c of both sides of euclid at c are equal.
    simpa [eval_add, eval_mul, eval_C, hc, hq] using this
  simp [hcoeff]
  done

example (p : ℚ[X]) (nz : p ≠ 0) : p.roots.card ≤ p.degree := by
  rw [degree_eq_natDegree nz] -- ⊢ p.roots.card ≤ p.natDegree
  induction' hp :  p.natDegree with n ih generalizing p
  · have peq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hp
    have h0 : p.roots.card ≤ 0 ↔ p.roots = ∅ := by simp
    rw_mod_cast [h0]

    sorry
  sorry



def p : ℚ[X] := C 5 * X ^ 2 + C 0 * X + C 3

lemma g_eq_p : g = p := by
  have h : 5 = ∑ x ∈ Finset.antidiagonal 2, if x.2 = 2 then if x.1 = 0 then 5 else 0 else 0 := by
    decide -- A result concerning the natural number `5` needed in some of the sequell
  ext n
  simp [g, p, coeff_C, coeff_mul]
  split_ifs with h₁ h₂ h₃
  · linarith
  · simp [h₁]
    exact_mod_cast h
  · simp [h₃]
  · have c3 : coeff ((C 3) : ℚ[X]) n = 0 := by
      rw [coeff_C]
      simpa
    have c31 : coeff (3 : ℚ[X]) n = 0 := by
      exact_mod_cast c3
    rw [c31]
    have nzero : (if n = 2 then (5 : ℚ) else 0) = 0 := by simp [h₁]
    have hzero :
      ∀ x ∈ Finset.antidiagonal n,
        (if x.2 = 2 then if x.1 = 0 then (5 : ℚ) else 0 else 0) = 0 := by
      intro x hx
      rcases x with ⟨i, k⟩
      by_cases hk : k = 2
      · by_cases hi : i = 0
        · have : i + k = n := (Finset.mem_antidiagonal.mp hx)
          have : n = 2 := by symm; simpa [hi, hk] using this
          contradiction
        · simp [hk, hi]
      · simp [hk]
    have : (∑ x ∈ Finset.antidiagonal n,
      (if x.2 = 2 then if x.1 = 0 then (5 : ℚ) else 0 else 0)) = 0 := by
        exact Finset.sum_eq_zero hzero
    simp [this]

example : g.degree = 2 := by
  rw [g_eq_p]
  apply degree_quadratic
  simp

lemma poly_division (f g : ℚ[X]) (gnz : g ≠ 0) :
  ∃ h r : ℚ[X], f = h * g + r ∧ (r.degree < g.degree) := by

  -- Use `by apply?` to find the proof below.
  have gdegeq : g.degree = g.natDegree := by exact degree_eq_natDegree gnz
  rw [gdegeq]
  by_cases hf: f = 0
  · use 0, 0
    simp [hf]
    -- use `by apply?` to find the proof below
    exact compareOfLessAndEq_eq_lt.mp rfl
  have fdegeq : f.degree = f.natDegree := by exact degree_eq_natDegree hf
  set m := f.natDegree with mdef
  set n := g.natDegree with ndef
  by_cases nlem : n ≤ m
  · induction' hp : m - n with k ih generalizing f
    · have mneq : n = m := by
        rw [Nat.sub_eq_zero_iff_le] at hp
        apply Nat.le_antisymm nlem hp
      set c := f.leadingCoeff / g.leadingCoeff
      use C c, f - C c * g
      sorry
    sorry
  use 0, f
  aesop


end section

#min_imports
