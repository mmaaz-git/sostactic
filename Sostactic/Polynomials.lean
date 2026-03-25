/-
Formalization of lemmas about multivariate polynomials over ℝ.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Order.Interval.Set.Infinite

open scoped Polynomial MvPolynomial
open Set Topology Filter

variable {n : ℕ}

/-!
## Lemma 1
Let f be a multivariate polynomial over ℝ of n variables.
Let a and v be two vectors in ℝ^n.
Then f(a + tv) is a single variable polynomial of t.
-/

/-- Evaluation of a multivariate polynomial along a line gives a univariate polynomial. -/
noncomputable def MvPolynomial.toPolynomialAlongLine (f : MvPolynomial (Fin n) ℝ)
    (a v : Fin n → ℝ) : Polynomial ℝ :=
  f.eval₂ Polynomial.C (fun i => Polynomial.C (a i) + Polynomial.X * Polynomial.C (v i))

theorem lemma1 (f : MvPolynomial (Fin n) ℝ) (a v : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (a + t • v) f =
    Polynomial.eval t (f.toPolynomialAlongLine a v) := by
  unfold MvPolynomial.toPolynomialAlongLine
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval₂_C, MvPolynomial.eval_C, Polynomial.eval_C]
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, mul_comm]

/-!
## Lemma 2
Let U be an open set in ℝ^n. Let p be a point in U. Let v be a vector in ℝ^n.
Then there exists some T > 0 such that p + tv is inside U for all t in the interval [0, T).
-/

theorem lemma2 (U : Set (Fin n → ℝ)) (hU : IsOpen U) (p : Fin n → ℝ) (hp : p ∈ U)
    (v : Fin n → ℝ) : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 ≤ t → t < T → p + t • v ∈ U := by
  -- Use continuity of the line map
  let line : ℝ → (Fin n → ℝ) := fun t => p + t • v
  have hcont : Continuous line := by
    apply Continuous.add continuous_const
    apply Continuous.smul continuous_id continuous_const
  have h0 : line 0 = p := by simp [line]
  obtain ⟨ε, hε_pos, hε⟩ := Metric.isOpen_iff.mp hU p hp
  -- Find T such that |t| < T implies line t ∈ U
  by_cases hv : v = 0
  · -- If v = 0, any T works since line is constant
    use 1
    constructor
    · linarith
    · intro t _ _
      simp only [hv, smul_zero, add_zero]
      apply hε
      simp [Metric.mem_ball, dist_self, hε_pos]
  · -- If v ≠ 0, use ε / ‖v‖
    have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    use ε / ‖v‖
    constructor
    · exact div_pos hε_pos hv_norm
    · intro t ht_ge ht_lt
      apply hε
      rw [Metric.mem_ball]
      have hdist : dist (p + t • v) p = ‖t • v‖ := by
        rw [dist_eq_norm]
        simp
      rw [hdist]
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg ht_ge]
      calc t * ‖v‖ < (ε / ‖v‖) * ‖v‖ := mul_lt_mul_of_pos_right ht_lt hv_norm
        _ = ε := div_mul_cancel₀ ε (ne_of_gt hv_norm)

/-!
## Lemma 3
Let f be a polynomial (of any number of variables) over ℝ.
Then f is the zero polynomial iff f is zero everywhere.

This follows from the fact that ℝ is an infinite integral domain.
-/

theorem lemma3 (f : MvPolynomial (Fin n) ℝ) :
    f = 0 ↔ ∀ x : Fin n → ℝ, MvPolynomial.eval x f = 0 := by
  constructor
  · intro h
    simp [h]
  · intro h
    exact MvPolynomial.funext (fun x => h x)

-- Single variable version of Lemma 3
theorem lemma3' (f : Polynomial ℝ) :
    f = 0 ↔ ∀ x : ℝ, Polynomial.eval x f = 0 := by
  constructor
  · intro h
    simp [h]
  · intro h
    by_contra hne
    -- f has infinitely many roots but only finitely many are possible
    -- The set of roots is all of ℝ
    have hsub : (Set.univ : Set ℝ) ⊆ (f.roots.toFinset : Set ℝ) := by
      intro x _
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact h x
    -- But ℝ is infinite and roots form a finite set
    have hfin : (Set.univ : Set ℝ).Finite :=
      Set.Finite.subset f.roots.toFinset.finite_toSet hsub
    exact Set.infinite_univ hfin

/-!
## Lemma 4
Let f be a single variable polynomial over ℝ.
If f is zero on some nonempty open interval (a, b), then f is zero everywhere.
-/

theorem lemma4 (f : Polynomial ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ t : ℝ, a < t → t < b → Polynomial.eval t f = 0) :
    f = 0 := by
  rw [lemma3']
  intro x
  by_cases hf : f = 0
  · rw [hf]; simp
  · exfalso
    -- f has at most deg(f) roots, but (a, b) contains infinitely many
    have hinf : (Set.Ioo a b).Infinite := Ioo_infinite hab
    have hsub : Set.Ioo a b ⊆ {x | Polynomial.eval x f = 0} := by
      intro t ⟨hat, htb⟩
      exact h t hat htb
    have hfin : {x | Polynomial.eval x f = 0}.Finite := by
      have hcontain : {x | Polynomial.eval x f = 0} ⊆ f.roots.toFinset := by
        intro y hy
        simp only [Set.mem_setOf_eq] at hy
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hf]
        exact hy
      exact Set.Finite.subset f.roots.toFinset.finite_toSet hcontain
    exact hinf (Set.Finite.subset hfin hsub)

/-!
## Lemma 5
Let f be a polynomial (of any number of variables) over ℝ.
If f is zero on some nonempty open set U, then f is zero everywhere.
-/

theorem lemma5 (f : MvPolynomial (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, MvPolynomial.eval x f = 0) :
    f = 0 := by
  rw [lemma3]
  intro x
  -- Take some p in U
  obtain ⟨p, hp⟩ := hne
  -- Let v = x - p
  set v := x - p with hv_def
  -- Consider g(t) = f(p + tv), a single variable polynomial
  set g := f.toPolynomialAlongLine p v with hg_def
  -- By Lemma 2, there exists T > 0 such that p + tv ∈ U for t ∈ [0, T)
  obtain ⟨T, hT_pos, hT⟩ := lemma2 U hU p hp v
  -- g is zero on (0, T)
  have hg_zero : ∀ t : ℝ, 0 < t → t < T → Polynomial.eval t g = 0 := by
    intro t ht_pos ht_lt
    rw [← lemma1]
    apply h
    exact hT t (le_of_lt ht_pos) ht_lt
  -- By Lemma 4, g is zero everywhere
  have hg_eq_zero : g = 0 := lemma4 g 0 T hT_pos hg_zero
  -- In particular, g(1) = 0
  have hg1 : Polynomial.eval (1 : ℝ) g = 0 := by rw [hg_eq_zero]; simp
  -- But g(1) = f(p + v) = f(x)
  have heval : MvPolynomial.eval (p + (1 : ℝ) • v) f = Polynomial.eval (1 : ℝ) g :=
    lemma1 f p v (1 : ℝ)
  rw [hg1, one_smul] at heval
  rw [hv_def, add_sub_cancel] at heval
  exact heval

/-!
## Lemma 6
Let f be a polynomial (of any number of variables) over ℝ that is not the zero polynomial.
Then the set of values on which f is nonzero is dense.
-/

theorem lemma6 (f : MvPolynomial (Fin n) ℝ) (hf : f ≠ 0) :
    Dense {x : Fin n → ℝ | MvPolynomial.eval x f ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  -- If {x | f(x) ≠ 0} ∩ U = ∅, then f is zero on U
  have hzero : ∀ x ∈ U, MvPolynomial.eval x f = 0 := by
    intro x hx
    by_contra hne'
    have hmem : x ∈ {x | MvPolynomial.eval x f ≠ 0} ∩ U := ⟨hne', hx⟩
    rw [Set.inter_comm] at hemp
    rw [hemp] at hmem
    exact hmem
  -- By Lemma 5, f = 0
  have := lemma5 f U hU hne hzero
  exact hf this

/-!
## Lemma 7
Let f be a continuous function on ℝ^n.
If f is nonnegative on a dense subset of ℝ^n, then f is nonnegative everywhere.
-/

theorem lemma7 (f : (Fin n → ℝ) → ℝ) (hcont : Continuous f)
    (S : Set (Fin n → ℝ)) (hS : Dense S)
    (hpos : ∀ x ∈ S, 0 ≤ f x) :
    ∀ x, 0 ≤ f x := by
  intro x
  -- x is in the closure of S
  have hx : x ∈ closure S := hS.closure_eq ▸ Set.mem_univ x
  -- Use continuity: f x is the limit of f on S
  rw [mem_closure_iff_seq_limit] at hx
  obtain ⟨seq, hseq_mem, hseq_lim⟩ := hx
  have hlim : Filter.Tendsto (f ∘ seq) Filter.atTop (nhds (f x)) :=
    hcont.continuousAt.tendsto.comp hseq_lim
  apply ge_of_tendsto hlim
  filter_upwards with i
  exact hpos (seq i) (hseq_mem i)

/-!
## Lemma 8
Let d, p, n be polynomials over ℝ of k variables.
Suppose that d is not the zero polynomial.
Suppose that d * p = n.
Suppose that d and n are both nonnegative on ℝ^n.
Then the set of values for which p is nonnegative is dense in ℝ^k.
-/

theorem lemma8 {k : ℕ} (d p nn : MvPolynomial (Fin k) ℝ)
    (hd_ne : d ≠ 0)
    (hmul : d * p = nn)
    (hd_nonneg : ∀ x, 0 ≤ MvPolynomial.eval x d)
    (hn_nonneg : ∀ x, 0 ≤ MvPolynomial.eval x nn) :
    Dense {x : Fin k → ℝ | 0 ≤ MvPolynomial.eval x p} := by
  -- The set where d is positive is dense by Lemma 6
  have hd_pos_dense : Dense {x | 0 < MvPolynomial.eval x d} := by
    have hsub : {x | MvPolynomial.eval x d ≠ 0} ⊆ {x | 0 < MvPolynomial.eval x d} := by
      intro x hx
      exact lt_of_le_of_ne (hd_nonneg x) (by simpa [eq_comm] using hx)
    exact Dense.mono hsub (lemma6 d hd_ne)
  -- Where d > 0, we have p = n/d ≥ 0
  have hsub : {x | 0 < MvPolynomial.eval x d} ⊆ {x | 0 ≤ MvPolynomial.eval x p} := by
    intro x hx
    have heq : MvPolynomial.eval x d * MvPolynomial.eval x p = MvPolynomial.eval x nn := by
      rw [← MvPolynomial.eval_mul, hmul]
    have hp_eq : MvPolynomial.eval x p = MvPolynomial.eval x nn / MvPolynomial.eval x d := by
      apply (eq_div_iff (ne_of_gt hx)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using heq
    simp only [Set.mem_setOf_eq]
    rw [hp_eq]
    exact div_nonneg (hn_nonneg x) (le_of_lt hx)
  exact Dense.mono hsub hd_pos_dense

/-!
## Nonnegativity from a nonnegative polynomial multiple
Let `d`, `p`, and `n` be polynomials over `ℝ` in `k` variables.
If `d` is not the zero polynomial, `d * p = n`, and both `d` and `n`
are pointwise nonnegative on `ℝ^k`, then `p` is pointwise nonnegative on `ℝ^k`.
-/

theorem nonneg_of_mul_of_nonneg_polynomials {k : ℕ} (d p nn : MvPolynomial (Fin k) ℝ)
    (hd_ne : d ≠ 0)
    (hmul : d * p = nn)
    (hd_nonneg : ∀ x, 0 ≤ MvPolynomial.eval x d)
    (hn_nonneg : ∀ x, 0 ≤ MvPolynomial.eval x nn) :
    ∀ x, 0 ≤ MvPolynomial.eval x p := by
  -- p is continuous
  have hcont : Continuous (fun x => MvPolynomial.eval x p) := MvPolynomial.continuous_eval p
  -- By Lemma 8, p is nonnegative on a dense set
  have hdense := lemma8 d p nn hd_ne hmul hd_nonneg hn_nonneg
  -- By Lemma 7, p is nonnegative everywhere
  exact lemma7 (fun x => MvPolynomial.eval x p) hcont _ hdense (fun x hx => hx)
