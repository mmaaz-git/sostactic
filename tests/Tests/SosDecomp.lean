import Sostactic

namespace Tests.SosDecomp

-- plain SOS (no denominator)
example (x y : ℝ) : 0 ≤ x^2 + y^2 := by sos_decomp

-- SOS with denominator (Motzkin)
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (degree := 2)

-- SOS with large rational certificates
set_option maxHeartbeats 800000 in
example (x1 x2 : ℝ) :
    0 ≤ 8 + (1 / 2 : ℝ) * x1^2 * x2^4 + x1^2 * x2^3 - 2 * x1^3 * x2^3 + 2 * x1 * x2^2
      + 10 * x1^2 * x2^2 + 4 * x1^3 * x2^2 + 3 * x1^4 * x2^2 + 4 * x1 * x2 - 8 * x1^2 * x2 := by
  sos_decomp (degree := 2)

end Tests.SosDecomp
