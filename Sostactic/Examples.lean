import Sostactic
import Sostactic.Polynomials

namespace Sostactic

-- Small Rump example
-- this is the general structure of a proof without a denominator
-- I prompted Codex to make a tactic that generates this proof in general
example (p0 p1 q0 q1 : ℝ) :
    0 ≤ (p0 * q0)^2 + (p0 * q1 + p1 * q0)^2 + (p1 * q1)^2
      - (1 / 2 : ℝ) * (p0^2 + p1^2) * (q0^2 + q1^2) := by
  have h_id: (p0 * q0)^2 + (p0 * q1 + p1 * q0)^2 + (p1 * q1)^2
          - (1 / 2 : ℝ) * (p0^2 + p1^2) * (q0^2 + q1^2)
        =
        (1 / 2 : ℝ) * (p0 * q0 + p1 * q1)^2
          + (1 / 2 : ℝ) * (p0 * q1 + p1 * q0)^2 := by
    ring_nf
  rw [h_id]
  positivity

-- the full Motzkin proof
-- this is the general structure of such a proof
-- I prompted Codex to make a tactic that generates this proof for general expr
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  let C : ℝ → MvPolynomial (Fin 3) ℝ := MvPolynomial.C
  let X0 : MvPolynomial (Fin 3) ℝ := MvPolynomial.X 0
  let X1 : MvPolynomial (Fin 3) ℝ := MvPolynomial.X 1
  let X2 : MvPolynomial (Fin 3) ℝ := MvPolynomial.X 2

  let P : MvPolynomial (Fin 3) ℝ :=
    X0^4 * X1^2 + X0^2 * X1^4 + X2^6 - C (3 : ℝ) * X0^2 * X1^2 * X2^2

  -- denominator returned by backend
  let D : MvPolynomial (Fin 3) ℝ :=
    C (1 / 4 : ℝ) * X0^2 + C (1 / 4 : ℝ) * X1^2 + C (1 / 2 : ℝ) * X2^2

  -- numerator returned by backend
  let N : MvPolynomial (Fin 3) ℝ :=
    C (1 / 2 : ℝ) * (-X0^2 * X1^2 + X2^4)^2
      + C (1 / 4 : ℝ) * (-X0^2 * X1 * X2 + X1 * X2^3)^2
      + C (1 / 4 : ℝ) * (-X0 * X1^2 * X2 + X0 * X2^3)^2
      + C (1 / 2 : ℝ) * (-C (1 / 2 : ℝ) * X0^3 * X1 - C (1 / 2 : ℝ) * X0 * X1^3 + X0 * X1 * X2^2)^2
      + C (1 / 8 : ℝ) * (-X0^3 * X1 + X0 * X1^3)^2

  have hD_ne : D ≠ 0 := by
    rw [MvPolynomial.ne_zero_iff]
    -- here, this is the witness monomial
    -- means we look for the monom of x2^2
    -- if we want the constant term, we instead do refine ⟨(0 : Fin 2 →₀ ℕ), ?_⟩
    refine ⟨Finsupp.single 2 2, ?_⟩

    dsimp [D, C, X0, X1, X2]
    simp [MvPolynomial.C_mul_X_pow_eq_monomial]
    grind -- not needed, if we choose the constant term

  have hmul : D * P = N := by
    apply MvPolynomial.funext
    intro v
    simp [D, P, N, C, X0, X1, X2]
    ring_nf

  have hD_nonneg : ∀ v : Fin 3 → ℝ, 0 ≤ MvPolynomial.eval v D := by
    intro v
    simp [D, C, X0, X1, X2]
    positivity

  have hN_nonneg : ∀ v : Fin 3 → ℝ, 0 ≤ MvPolynomial.eval v N := by
    intro v
    simp [N, C, X0, X1, X2]
    positivity

  have hP_nonneg :
      ∀ v : Fin 3 → ℝ, 0 ≤ MvPolynomial.eval v P :=
    nonneg_of_mul_of_nonneg_polynomials D P N hD_ne hmul hD_nonneg hN_nonneg

  simpa [P, C, X0, X1, X2] using hP_nonneg ![x, y, z]

-- motzkin with sos_decomp
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
    sos_decomp (degree := 2)

-- motzkin with a denominator template
example (x y z : ℝ) :
  0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
    sos_decomp (degree := 2) (denom_template := "a*x^2 + b*y^2 + c*z^2")

-- leepstarr2 with sos_decomp (large rational certificates require extra heartbeats)
set_option maxHeartbeats 800000 in
example (x1 x2 : ℝ) :
    0 ≤ 8 + (1 / 2 : ℝ) * x1^2 * x2^4 + x1^2 * x2^3 - 2 * x1^3 * x2^3 + 2 * x1 * x2^2
      + 10 * x1^2 * x2^2 + 4 * x1^3 * x2^2 + 3 * x1^4 * x2^2 + 4 * x1 * x2 - 8 * x1^2 * x2 := by
    sos_decomp (degree := 2)

-- AM-GM: sos_decomp handles a ≤ b goals, not just 0 ≤ f
example (x y : ℝ) : 2 * x * y ≤ x^2 + y^2 := by
  sos_decomp

-- easy: x*(1-x) >= 0 on [0, 1]
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (order := 1)

-- easy: 4x^3 - 3x + 1 >= 0 on [0, 1] (touches 0 at x = 1/2)
-- linarith, positivity, and nlinarith all fail
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (order := 2)

-- {x >= 0, x <= -1} is empty
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ -x - 1) : False := by
  putinar_empty (order := 1)

-- inside unit disk and outside sqrt(2)-disk is empty
example (x y : ℝ) (h1 : 0 ≤ 1 - x^2 - y^2) (h2 : 0 ≤ x^2 + y^2 - 2) : False := by
  schmudgen_empty (order := 1)

-- two disjoint disks centered at (0,0) and (3,3)
-- linarith and nlinarith fail
example : ¬∃ x y : ℝ, 0 ≤ 1 - x^2 - y^2 ∧ 0 ≤ 1 - (x - 3)^2 - (y - 3)^2 := by
  rintro ⟨x, y, h1, h2⟩
  schmudgen_empty (order := 1)

/-
Theorem.
Every point in the heart (x^2+y^2-1)^3 - x^2*y^3 <= 0 lies in the disk of radius 2

This is 'too hard' to prove immediately with a psatz certificate.
So we split by cases, using the box {-2<=x<=2, -2<=y<=2}.
This helps because this makes the set Archimedean, so can use Putinar.
-/
set_option maxHeartbeats 1600000 in
example (x y : ℝ) (h1 : (x^2+y^2-1)^3 ≤ x^2*y^3) : x^2 + y^2 ≤ 4 := by
  by_cases h3 : x^2 ≤ 4
  · by_cases h4 : y^2 ≤ 4
    · -- main case: box holds, use degree-4 certificate
      -- translated to relaxation order 5
      by_contra h2; push_neg at h2
      have h2' : x^2 + y^2 ≥ 4 := by linarith
      putinar_empty (order := 5)
    · -- y^2 > 4: contradict heart curve with just {heart, y^2≥4}
      push_neg at h4
      have h4' : y^2 ≥ 4 := by linarith
      exfalso
      putinar_empty (order := 6) (block_bases := "1:2")
  · -- x^2 > 4: contradict heart curve with just {heart, x^2≥4}
    push_neg at h3
    have h3' : x^2 ≥ 4 := by linarith
    exfalso
    putinar_empty (order := 6) (block_bases := "1:2")

example (x y z : ℝ) :
  0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
    sos_decomp (degree := 2) (denom_template := "a*x^2 + b*y^2 + c*z^2")

end Sostactic
