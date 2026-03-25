import Sostactic

namespace Tests.IneqForms

-- sos_decomp: 0 ≤ f
example (x y : ℝ) : 0 ≤ x^2 + y^2 := by sos_decomp

-- sos_decomp: a ≤ b
example (x y : ℝ) : 2 * x * y ≤ x^2 + y^2 := by sos_decomp

-- sos_decomp: f ≥ 0
example (x y : ℝ) : x^2 + y^2 ≥ 0 := by sos_decomp

-- sos_decomp: a ≥ b
example (x y : ℝ) : x^2 + y^2 ≥ 2 * x * y := by sos_decomp

-- schmudgen_decomp: constraint as 0 ≤ f
example (x : ℝ) (h : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (degree := 0)

-- schmudgen_decomp: constraint as a ≤ b
example (x : ℝ) (h : 0 ≤ x) (h2 : x ≤ 1) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (degree := 0)

-- schmudgen_decomp: constraint as a ≥ b
example (x : ℝ) (h : x ≥ 0) (h2 : 1 ≥ x) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (degree := 0)

-- schmudgen_decomp: goal as f ≥ 0 with ≥ constraints
example (x : ℝ) (h : x ≥ 0) (h2 : 1 ≥ x) :
    x * (1 - x) ≥ 0 := by
  schmudgen_decomp (degree := 0)

-- putinar_empty: constraints as a ≤ b
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ -1) : False := by
  putinar_empty (degree := 0)

-- putinar_empty: constraints as a ≥ b
example (x : ℝ) (h1 : x ≥ 0) (h2 : -1 ≥ x) : False := by
  putinar_empty (degree := 0)

-- schmudgen_empty: mixed ≤ and ≥
example (x y : ℝ) (h1 : x^2 + y^2 ≤ 1) (h2 : x^2 + y^2 ≥ 2) : False := by
  schmudgen_empty (degree := 2)

-- putinar_decomp: goal as a ≤ b, constraints mixed
example (x : ℝ) (h1 : x ≥ 0) (h2 : x ≤ 1) : 2 * x ≤ x^2 + 1 := by
  putinar_decomp (degree := 2)

end Tests.IneqForms
