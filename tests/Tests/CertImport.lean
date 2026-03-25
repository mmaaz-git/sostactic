import Sostactic

namespace Tests.CertImport

-- sos_decomp: plain SOS from cert
example (x y : ℝ) : 0 ≤ x^2 + y^2 := by
  sos_decomp (cert := "certs/simple_sos.json")

-- sos_decomp: a ≤ b from cert
example (x y : ℝ) : 2 * x * y ≤ x^2 + y^2 := by
  sos_decomp (cert := "certs/amgm_sos.json")

-- schmudgen_decomp from cert
example (x : ℝ) (h : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (cert := "certs/unit_interval.json")

-- putinar_empty from cert
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ -x - 1) : False := by
  putinar_empty (cert := "certs/empty_set.json")

end Tests.CertImport
