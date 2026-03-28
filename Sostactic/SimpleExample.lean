import Sostactic
import Sostactic.Polynomials

namespace Sostactic

example (x y : ℝ) : 0 ≤ x^2 + y^2 := by
  sos_decomp
  --case sos_identity => ring_nf
  --case sos_nonneg => positivity
