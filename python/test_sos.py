import pytest

import sympy as sp
import json
import subprocess
import sys
from pathlib import Path
from sympy.abc import x, y, z
a, b = sp.symbols("a b")

from python.sos import (
    compile_sos_affine_system,
    exactify_sos_solution,
    make_in_polytope,
    monomial_basis_from_support,
    numeric_sos_solution,
    putinar,
    putinar_empty,
    schmudgen,
    schmudgen_empty,
    sos_decomp,
    tuples_sum_leq,
)


def test_tuples_sum_leq():
    assert list(tuples_sum_leq(2, 2)) == [
        (0, 0),
        (0, 1),
        (1, 0),
        (0, 2),
        (1, 1),
        (2, 0),
    ]


def test_make_in_polytope():
    in_polytope = make_in_polytope([(0, 0), (2, 0), (0, 2)]) # a triangle

    assert in_polytope((1, 1))
    assert in_polytope((2, 0))
    assert not in_polytope((2, 2))


def test_monomial_basis_from_support():
    support = [(2, 0), (1, 1), (0, 2)]

    assert monomial_basis_from_support(support) == [(0, 1), (1, 0)]
    with pytest.raises(ValueError, match="support must be nonempty"):
        monomial_basis_from_support([])
    with pytest.raises(ValueError, match="support must have even total degree"):
        monomial_basis_from_support([(1, 0), (0, 1)])


def test_numeric_sos_solution():
    res = numeric_sos_solution(sp.Poly(x**2 + y**2, x, y))

    assert res["status"] == "optimal"
    assert res["basis"] == [(0, 1), (1, 0)]
    assert res["A"] == sp.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    assert res["b"] == sp.Matrix([1, 0, 1, 1])
    assert res["gram"].shape == (2, 2)
    assert res["gram"][0, 0] == pytest.approx(1.0)
    assert res["gram"][0, 1] == pytest.approx(0.0)
    assert res["gram"][1, 0] == pytest.approx(0.0)
    assert res["gram"][1, 1] == pytest.approx(1.0)

    templated = numeric_sos_solution(
        sp.Poly(x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2, x, y, z),
        denom_template=sp.Poly(a*x**2 + b*y**2, x, y, z),
    )
    assert templated["status"] == "optimal"
    assert templated["param_symbols"] == (a, b)


def test_compile_sos_affine_system():
    res = compile_sos_affine_system(sp.Poly(x**2 + y**2, x, y))
    assert res["basis"] == [(0, 1), (1, 0)]
    assert res["upper_indices"] == [(0, 0), (0, 1), (1, 1)]
    assert res["A"] == sp.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    assert res["b"] == sp.Matrix([1, 0, 1, 1])

    res = compile_sos_affine_system(sp.Poly(x**2 + y**2, x, y), denom_degree_bound=2)
    assert res["den_basis"] == [(0, 0), (0, 1), (1, 0)]
    assert res["A"].cols == len(res["num_upper_indices"]) + len(res["den_upper_indices"])
    assert res["b"].rows == res["A"].rows

    templated = compile_sos_affine_system(
        sp.Poly(x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2, x, y, z),
        denom_template=sp.Poly(a*x**2 + a*y**2, x, y, z),
    )
    assert templated["den_basis"] == [(0, 1, 0), (1, 0, 0)]
    assert templated["param_symbols"] == (a,)

    with pytest.raises(ValueError, match="linear"):
        compile_sos_affine_system(
            sp.Poly(x**2 + y**2, x, y),
            denom_template=sp.Poly(a**2 * x**2, x, y),
        )


def test_exactify_sos_solution():
    res = exactify_sos_solution(numeric_sos_solution(sp.Poly(x**2 + y**2, x, y)))
    assert res["success"]
    assert res["exact_gram"] == sp.Matrix([[1, 0], [0, 1]])
    assert res["exact_num_poly"] == sp.Poly(x**2 + y**2, x, y)
    assert res["exact_den_gram"] == sp.Matrix([[1]])
    assert res["exact_sos"] == [(1, sp.Poly(y, x, y)), (1, sp.Poly(x, x, y))]
    assert res["max_denominator"] == 1

    block_res = exactify_sos_solution(numeric_sos_solution(sp.Poly(x**2 + y**2, x, y), denom_degree_bound=2))
    assert block_res["success"]
    assert block_res["exact_num_gram"].rows == len(block_res["num_basis"])
    assert block_res["exact_den_gram"].rows == len(block_res["den_basis"])


def test_sos_decomp():
    x1, x2 = sp.symbols("x1 x2")
    p0, p1, p2, q0, q1, q2 = sp.symbols("p0 p1 p2 q0 q1 q2")
    # x^4 + 2*x^2 + 1
    res = sos_decomp(sp.Poly(x**4 + 2*x**2 + 1, x))
    assert res["success"]

    # x^6 + x^2
    res = sos_decomp(sp.Poly(x**6 + x**2, x))
    assert res["success"]

    # x^2 + y^2
    res = sos_decomp(sp.Poly(x**2 + y**2, x, y))
    assert res["success"]
    assert res["exact_gram"] == sp.Matrix([[1, 0], [0, 1]])

    # x^4 + y^4
    res = sos_decomp(sp.Poly(x**4 + y**4, x, y))
    assert res["success"]

    # (x + y)^2 + (x - 2*y)^2
    res = sos_decomp(sp.Poly((x + y)**2 + (x - 2*y)**2, x, y))
    assert res["success"]

    # x^4 + 2*x^2*y^2 + y^4
    res = sos_decomp(sp.Poly(x**4 + 2*x**2*y**2 + y**4, x, y))
    assert res["success"]

    # x^4 + x^2*y^2 + y^4
    res = sos_decomp(sp.Poly(x**4 + x**2*y**2 + y**4, x, y))
    assert res["success"]

    # (x^2 - y)^2 + (x*y - 1)^2
    res = sos_decomp(sp.Poly((x**2 - y)**2 + (x*y - 1)**2, x, y))
    assert res["success"]

    # (x^2 + y^2 - 1)^2 + (2*x*y)^2
    res = sos_decomp(sp.Poly((x**2 + y**2 - 1)**2 + (2*x*y)**2, x, y))
    assert res["success"]

    # (x^2 + y^2 + z^2)^2
    res = sos_decomp(sp.Poly((x**2 + y**2 + z**2)**2, x, y, z))
    assert res["success"]

    # rump n = 2
    rump_poly = sp.Poly(
        sp.expand(
            (p0*q0)**2
            + (p0*q1 + p1*q0)**2
            + (p1*q1)**2
            - sp.Rational(1, 2) * (p0**2 + p1**2) * (q0**2 + q1**2)
        ),
        p0, p1, q0, q1,
    )
    res = sos_decomp(rump_poly)
    assert res["success"]
    assert res["exact_gram"] == sp.Matrix([
        [sp.Rational(1, 2), 0, 0, sp.Rational(1, 2)],
        [0, sp.Rational(1, 2), sp.Rational(1, 2), 0],
        [0, sp.Rational(1, 2), sp.Rational(1, 2), 0],
        [sp.Rational(1, 2), 0, 0, sp.Rational(1, 2)],
    ])

    # Rump's model problem
    # prove ||P Q||^2 >= (1/9) * ||P||^2 * ||Q||^2 for deg(P), deg(Q) <= 2
    # this is mu_3 = 1/9 from Rump, Table I
    coeffs = [
        p0*q0,
        p0*q1 + p1*q0,
        p0*q2 + p1*q1 + p2*q0,
        p1*q2 + p2*q1,
        p2*q2,
    ]
    rump_poly = sp.Poly(
        sp.expand(
            sum(c**2 for c in coeffs)
            - sp.Rational(1, 9) * (p0**2 + p1**2 + p2**2) * (q0**2 + q1**2 + q2**2)
        ),
        p0, p1, p2, q0, q1, q2,
    )
    res = sos_decomp(rump_poly)
    assert res["success"]

    # leepstarr2
    res = sos_decomp(
        sp.Poly(
            8 + sp.Rational(1, 2)*x1**2*x2**4 + x1**2*x2**3 - 2*x1**3*x2**3 + 2*x1*x2**2
            + 10*x1**2*x2**2 + 4*x1**3*x2**2 + 3*x1**4*x2**2 + 4*x1*x2 - 8*x1**2*x2,
            x1, x2,
        ),
        denom_degree_bound=2,
    )
    assert res["success"]
    assert res["exact_den_gram"] == sp.Matrix([
        [sp.Rational(1, 3), 0, 0],
        [0, sp.Rational(1, 3), 0],
        [0, 0, sp.Rational(1, 3)],
    ])

    # motzkin
    res = sos_decomp(
        sp.Poly(x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2, x, y, z),
        denom_degree_bound=2,
    )
    assert res["success"]
    assert res["exact_den_gram"] == sp.Matrix([
        [0, 0, 0, 0],
        [0, sp.Rational(1, 2), 0, 0],
        [0, 0, sp.Rational(1, 4), 0],
        [0, 0, 0, sp.Rational(1, 4)],
    ])
    assert res["exact_den_nonzero_coeff_witness"] == {
        "exponents": [0, 0, 2],
        "coeff": "1/2",
    }

    # motzkin with a template
    res = sos_decomp(
        sp.Poly(x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2, x, y, z),
        denom_template=sp.Poly(a*x**2 + b*y**2, x, y, z),
    )
    assert res["success"]
    assert res["exact_param_values"] == {a: sp.Rational(1, 2), b: sp.Rational(1, 2)}

    # scaled motzkin with a template (currently does not pass with no-template)
    res = sos_decomp(
        sp.Poly(9*x**4*y**2 + 81*x**2*y**4 + 729*z**6 - 243*x**2*y**2*z**2, x, y, z),
        denom_template=sp.Poly(a*x**2 + b*y**2, x, y, z),
    )
    assert res["success"]
    assert res["exact_param_values"] == {a: sp.Rational(1, 10), b: sp.Rational(9, 10)}


def test_putinar():
    # x >= 0 and x <= -1
    gs = [sp.Poly(x, x), sp.Poly(-x - 1, x)]

    res = putinar_empty(gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(-1, x)
    assert res["exact_residual"] == sp.Poly(0, x)
    assert len(res["exact_certificate_blocks"]) == 3

    # inside the unit disk and outside the sqrt(2)-disk
    gs = [sp.Poly(1 - x**2 - y**2, x, y), sp.Poly(x**2 + y**2 - 2, x, y)]

    res = putinar_empty(gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(-1, x, y)
    assert res["exact_residual"] == sp.Poly(0, x, y)

    # x >= 0 on [0, 1]
    gs = [sp.Poly(x, x), sp.Poly(1 - x, x)]

    res = putinar(sp.Poly(x, x), gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(x, x)
    assert res["exact_residual"] == sp.Poly(0, x)

    # x*y >= 0 on the triangle {x >= 0, y >= 0, 1-x-y >= 0}
    # The triangle is compact so the quadratic module is Archimedean — Putinar's
    # theorem guarantees a certificate exists. However, it requires impractically
    # high relaxation order, so the solver still fails at order=3. Schmudgen
    # finds it at order=1 (see test_schmudgen) because it has the
    # cross-term multiplier x*y built in.
    gs = [sp.Poly(x, x, y), sp.Poly(y, x, y), sp.Poly(1 - x - y, x, y)]

    res = putinar(sp.Poly(x * y, x, y), gs, order=3)
    assert not res["success"]

    # Scheiderer's Example 2.3.6: K = {x >= 1/2, y >= 1/2, xy <= 1} is compact,
    # but M = QM(2x-1, 2y-1, 1-xy) is NOT Archimedean. So c - x^2 - y^2 is
    # positive on K for c > 2, but is genuinely not in the quadratic module —
    # Putinar's theorem does not apply here.
    gs = [sp.Poly(2*x - 1, x, y), sp.Poly(2*y - 1, x, y), sp.Poly(1 - x*y, x, y)]

    res = putinar(sp.Poly(5 - x**2 - y**2, x, y), gs, order=3)
    assert not res["success"]


def test_schmudgen():
    # x >= 0 and x <= -1
    gs = [sp.Poly(x, x), sp.Poly(-x - 1, x)]

    res = schmudgen_empty(gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(-1, x)
    assert res["exact_residual"] == sp.Poly(0, x)
    assert len(res["exact_certificate_blocks"]) == 4

    # inside the unit disk and outside the sqrt(2)-disk
    gs = [sp.Poly(1 - x**2 - y**2, x, y), sp.Poly(x**2 + y**2 - 2, x, y)]

    res = schmudgen_empty(gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(-1, x, y)
    assert res["exact_residual"] == sp.Poly(0, x, y)

    # x * (1 - x) >= 0 on [0, 1]
    gs = [sp.Poly(x, x), sp.Poly(1 - x, x)]

    res = schmudgen(sp.Poly(x * (1 - x), x), gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(x - x**2, x)
    assert res["exact_residual"] == sp.Poly(0, x)

    # x*y >= 0 on the triangle {x >= 0, y >= 0, 1-x-y >= 0}
    # The certificate is x*y = (x*y) * 1, using the cross-term multiplier g1*g2.
    # Putinar fails on this at practical orders (see test_putinar) — a
    # Putinar certificate exists (the set is Archimedean) but requires very high
    # order. Schmudgen finds it immediately because it has product multipliers.
    gs = [sp.Poly(x, x, y), sp.Poly(y, x, y), sp.Poly(1 - x - y, x, y)]

    res = schmudgen(sp.Poly(x * y, x, y), gs, order=1)
    assert res["success"]
    assert res["exact_identity"] == sp.Poly(x * y, x, y)
    assert res["exact_residual"] == sp.Poly(0, x, y)

def test_cli():
    script = Path(__file__).with_name("sos.py")

    # sos_decomp
    proc = subprocess.run(
        [sys.executable, str(script), "sos_decomp", "--poly", "x**2 + y**2", "--vars", "x y"],
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["success"]
    assert payload["exact_num_poly"]["expr"] == "x**2 + y**2"
    assert len(payload["exact_sos"]) == 2

    # putinar
    proc = subprocess.run(
        [sys.executable, str(script), "putinar", "--constraints", "x, -x-1", "--vars", "x", "--order", "1"],
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["success"]
    assert payload["exact_identity"]["expr"] == "-1"
    assert len(payload["exact_certificate_blocks"]) == 3

    # putinar with a target polynomial
    proc = subprocess.run(
        [sys.executable, str(script), "putinar", "--poly", "x", "--constraints", "x, 1 - x", "--vars", "x", "--order", "1"],
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["success"]
    assert payload["exact_identity"]["expr"] == "x"
