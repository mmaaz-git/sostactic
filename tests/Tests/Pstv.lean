import Sostactic

namespace Tests.Pstv

-- putinar_decomp: nonneg on [0, 1]
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (order := 2)

-- putinar_empty: contradictory constraints
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ -x - 1) : False := by
  putinar_empty (order := 1)

-- putinar_decomp: exactification rescue via basis_overrides
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ x := by
  putinar_decomp (order := 2) (basis_overrides := "0:0")

-- schmudgen_decomp: nonneg on [0, 1]
example (x : ℝ) (h : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (order := 1)

-- schmudgen_empty: disjoint disks
example (x y : ℝ) (h1 : 0 ≤ 1 - x^2 - y^2) (h2 : 0 ≤ x^2 + y^2 - 2) : False := by
  schmudgen_empty (order := 1)

-- putinar_empty via ¬∃
example : ¬∃ x y : ℝ, 0 ≤ 1 - x^2 - y^2 ∧ 0 ≤ 1 - (x - 3)^2 - (y - 3)^2 := by
  rintro ⟨x, y, h1, h2⟩
  schmudgen_empty (order := 1)

end Tests.Pstv
