import sympy as sp
from sympy.abc import x, y, z
import numpy as np
import cvxpy as cp
import argparse
import json
import sys
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product

# UTILS

def tuples_sum_leq(n_elems: int, target: int):
    """
    Generates all tuples of length n_elems that sum to <=target.
    """
    t = [0] * n_elems

    def rec(i, remaining):
        if i == n_elems - 1:
            t[i] = remaining
            yield tuple(t)
            return
        for v in range(remaining + 1):
            t[i] = v
            yield from rec(i + 1, remaining - v)

    for total in range(target + 1):
        yield from rec(0, total)

def make_in_polytope(support: list[tuple[int, ...]]):
    """
    Return a function that checks membership in conv(support).
    Helpful for repeatedly checking membership in `support`.
    """
    V = np.asarray(support, dtype=float)
    k, n = V.shape

    w = cp.Variable(k, nonneg=True)
    x = cp.Parameter(n)

    prob = cp.Problem(cp.Minimize(0.0), [V.T @ w == x, cp.sum(w) == 1])

    def in_polytope(point: tuple[int, ...]) -> bool:
        x.value = np.asarray(point, dtype=float)
        prob.solve(solver=cp.CLARABEL, verbose=False)
        return prob.status in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE)

    return in_polytope

def monomial_basis_from_support(support: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    """
    Return the Newton-pruned SOS monomial basis for a polynomial with the given
    support. A monomial e is kept iff 2e lies in the convex hull of `support`.
    The convex hull of monomials' exponent tuples is called the "Newton polytope".
    """
    if not support:
        raise ValueError("support must be nonempty")

    nvars = len(support[0])
    total_degree = max(sum(mon) for mon in support)
    if total_degree % 2 != 0:
        raise ValueError("support must have even total degree")
    d = total_degree // 2

    mins = [min(m[i] for m in support) for i in range(nvars)]
    maxs = [max(m[i] for m in support) for i in range(nvars)]
    in_polytope = make_in_polytope(support)

    basis = []
    for e in tuples_sum_leq(nvars, d):
        etimes2 = tuple(2 * _ for _ in e)
        if any(etimes2[i] < mins[i] or etimes2[i] > maxs[i] for i in range(nvars)):
            continue
        if in_polytope(etimes2):
            basis.append(e)
    return basis

def make_minkowski_sum(support_a: list[tuple[int, ...]], support_b: list[tuple[int, ...]]):
    """
    Return the Minkowski sum of two supports.
    """
    return sorted({
        tuple(a + b for a, b in zip(alpha, beta))
        for alpha in support_a
        for beta in support_b
    })

def monomial_basis_with_degree_bound(nvars: int, degree_bound: int):
    """
    Return all monomials with total degree at most degree_bound // 2.
    """
    return list(tuples_sum_leq(nvars, degree_bound // 2))

def _upper_indices(size: int):
    """
    Return the upper-triangular indices of a square matrix.
    """
    return [(i, j) for i in range(size) for j in range(i, size)]

def _gram_rows_by_mon(basis, upper_indices):
    """
    Return the coefficient rows for m^T Q m in upper-triangular coordinates.
    """
    rows_by_mon = defaultdict(lambda: [0] * len(upper_indices))
    for k, (i, j) in enumerate(upper_indices):
        mon = tuple(ai + bi for ai, bi in zip(basis[i], basis[j]))
        rows_by_mon[mon][k] += 1 if i == j else 2
    return rows_by_mon

def _reduce_affine_system(A: sp.Matrix, b: sp.Matrix):
    """
    Row-reduce the affine system A q = b.
    """
    aug = A.row_join(b)
    rref_aug, pivots = aug.rref()
    if any(pivot == A.cols for pivot in pivots):
        raise ValueError("affine system is inconsistent")
    A = sp.Matrix([rref_aug[i, :-1] for i in range(len(pivots))])
    b = sp.Matrix([rref_aug[i, -1] for i in range(len(pivots))])
    return A, b

def _poly_from_coeffs(coeffs: dict, gens):
    """
    Build a polynomial expression from its coefficient dictionary.
    """
    expr = 0
    for mon, coeff in coeffs.items():
        term = coeff
        for g, e in zip(gens, mon):
            term *= g**e
        expr += term
    return sp.expand(expr)

def _poly(expr, gens):
    """
    Build a Poly with a fixed generator order.
    """
    return sp.Poly(expr.as_expr() if isinstance(expr, sp.Poly) else sp.expand(expr), *gens)

def _common_gens(polys):
    """
    Return the sorted generators appearing in polys.
    """
    symbols = set()
    for poly in polys:
        expr = poly.as_expr() if isinstance(poly, sp.Poly) else sp.expand(poly)
        symbols |= expr.free_symbols
    return tuple(sorted(symbols, key=sp.default_sort_key))

def _block_coeffs(q_block, rows_by_mon: dict):
    """
    Return the polynomial coefficients induced by q_block.
    """
    coeffs = {}
    for mon, row in rows_by_mon.items():
        coeffs[mon] = sum(c * v for c, v in zip(row, q_block))
    return coeffs

def _template_data(denom_template, gens):
    """
    Return the polynomial and parameter data for a denominator template.
    """
    template_poly = _poly(denom_template, gens)
    template_coeffs = {
        mon: sp.expand(coeff) for mon, coeff in template_poly.as_dict().items()
    }
    param_symbols = tuple(sorted(template_poly.free_symbols - set(gens), key=sp.default_sort_key))
    if param_symbols:
        zero_subs = {sym: 0 for sym in param_symbols}
        for coeff in template_coeffs.values():
            try:
                coeff_poly = sp.Poly(coeff, *param_symbols)
            except sp.PolynomialError as exc:
                raise ValueError("template coefficients must be polynomial in the template parameters") from exc
            if coeff_poly.total_degree() > 1:
                raise ValueError("template coefficients must be linear in the template parameters")
        trace_normalization = all(coeff.subs(zero_subs) == 0 for coeff in template_coeffs.values())
    else:
        trace_normalization = False
    return template_poly, template_coeffs, param_symbols, trace_normalization

# BACKEND

def _prepare_certificate_blocks(blocks: list[dict]):
    """
    Add basis and coordinate data to each certificate block.
    """
    prepared = []
    offset = 0
    for block in blocks:
        upper_indices = _upper_indices(len(block["basis"]))
        rows_by_mon = dict(_gram_rows_by_mon(block["basis"], upper_indices))
        size = len(upper_indices)
        prepared.append({
            **block,
            "upper_indices": upper_indices,
            "rows_by_mon": rows_by_mon,
            "slice": slice(offset, offset + size),
        })
        offset += size
    return prepared

def _compile_certificate_affine_system(
    target: sp.Poly,
    blocks: list[dict],
    param_symbols: tuple = (),
    extra_rows: list[list] | None = None,
    extra_rhs: list | None = None,
):
    """
    Compile the affine system sum_i h_i sigma_i = target.
    """
    if extra_rows is None:
        extra_rows = []
    if extra_rhs is None:
        extra_rhs = []

    blocks = _prepare_certificate_blocks(blocks)
    block_width = sum(len(block["upper_indices"]) for block in blocks)
    total_cols = block_width + len(param_symbols)

    monoms = set(target.as_dict())
    for block in blocks:
        monoms |= set(make_minkowski_sum(list(block["multiplier"].as_dict()), list(block["rows_by_mon"])))

    rows = []
    rhs = []
    for mon in sorted(monoms):
        row = [0] * total_cols
        for block in blocks:
            coeffs = block["multiplier"].as_dict()
            for alpha, ha in coeffs.items():
                beta = tuple(mi - ai for mi, ai in zip(mon, alpha))
                if any(bi < 0 for bi in beta):
                    continue
                sigma_row = block["rows_by_mon"].get(beta)
                if sigma_row is None:
                    continue
                for j, coeff in enumerate(sigma_row):
                    row[block["slice"].start + j] += ha * coeff
        rows.append(row)
        rhs.append(target.as_dict().get(mon, 0))

    A = sp.Matrix(rows + extra_rows)
    b = sp.Matrix(rhs + extra_rhs)
    A, b = _reduce_affine_system(A, b)
    return {
        "target": target,
        "gens": target.gens,
        "blocks": blocks,
        "param_symbols": param_symbols,
        "A": A,
        "b": b,
    }

def _upper_vec(Q, upper_indices):
    """
    Flatten the upper triangle of Q using upper_indices.
    """
    return np.asarray([Q[i, j] for i, j in upper_indices], dtype=float)

def _vec_to_sym_matrix(q, size: int, upper_indices):
    """
    Rebuild a symmetric matrix from its upper-triangular entries.
    """
    Q = sp.zeros(size, size)
    for val, (i, j) in zip(q, upper_indices):
        Q[i, j] = val
        Q[j, i] = val
    return Q

def _gram_factor(Q: np.ndarray):
    """
    Return a PSD factor C with Q ~= C^T C.
    """
    evals, evecs = np.linalg.eigh(0.5 * (Q + Q.T))
    evals = np.clip(evals, 0.0, None)
    return np.diag(np.sqrt(evals)) @ evecs.T

def _project_to_affine_space_exact(q0: sp.Matrix, A: sp.Matrix, b: sp.Matrix):
    """
    Project q0 exactly onto the affine space A q = b.
    """
    residual = A * q0 - b
    if residual == sp.zeros(*residual.shape):
        return q0
    y = (A * A.T).LUsolve(residual)
    return sp.Matrix(q0 - A.T * y)

def _exact_psd(Q: sp.Matrix):
    """
    Check exact PSD via LDL decomposition (pure rational arithmetic).

    Sympy's built-in ``is_positive_semidefinite`` uses Cholesky which
    computes square roots of rationals and can overflow on large entries.
    LDL only needs division, so it stays in ℚ.
    """
    n = Q.rows
    L = sp.eye(n)
    D = [sp.S.Zero] * n
    for i in range(n):
        D[i] = Q[i, i] - sum(L[i, k]**2 * D[k] for k in range(i))
        if D[i] < 0:
            return False
        if D[i] == 0:
            # rest of column must be zero
            for j in range(i + 1, n):
                val = Q[j, i] - sum(L[j, k] * L[i, k] * D[k] for k in range(i))
                if val != 0:
                    return False
        else:
            for j in range(i + 1, n):
                L[j, i] = (Q[j, i] - sum(L[j, k] * L[i, k] * D[k] for k in range(i))) / D[i]
    return True

def _factor_jacobian(A, C, upper_indices):
    """
    Return the Jacobian of A q(C^T C) with respect to C.
    """
    J = np.zeros((A.shape[0], C.shape[0] * C.shape[1]))
    for r in range(C.shape[0]):
        for j in range(C.shape[1]):
            dq = np.zeros(len(upper_indices))
            for k, (u, v) in enumerate(upper_indices):
                if u == j == v:
                    dq[k] = 2 * C[r, j]
                elif u == j:
                    dq[k] = C[r, v]
                elif v == j:
                    dq[k] = C[r, u]
            J[:, r * C.shape[1] + j] = A @ dq
    return J

def _q_numeric(sol: dict):
    """
    Return the concatenated numeric variable vector.
    """
    parts = [
        _upper_vec(Q, block["upper_indices"])
        for Q, block in zip(sol["block_grams"], sol["blocks"])
    ]
    if sol["param_symbols"]:
        parts.append(np.asarray([sol["param_values"][sym] for sym in sol["param_symbols"]], dtype=float))
    return np.concatenate(parts)

def _exact_block_grams(q_exact: sp.Matrix, blocks: list[dict]):
    """
    Return the exact Gram blocks contained in q_exact.
    """
    grams = []
    for block in blocks:
        q_block = q_exact[block["slice"], :]
        grams.append(_vec_to_sym_matrix(q_block, len(block["basis"]), block["upper_indices"]))
    return grams

def _block_poly_from_gram(Q: sp.Matrix, block: dict):
    """
    Return the SOS polynomial represented by a block Gram matrix.
    """
    q_block = [Q[i, j] for i, j in block["upper_indices"]]
    coeffs = _block_coeffs(q_block, block["rows_by_mon"])
    return _poly(_poly_from_coeffs(coeffs, block["multiplier"].gens), block["multiplier"].gens)

def _basis_poly(coeffs, basis, gens):
    """
    Build a polynomial from basis coefficients.
    """
    expr = 0
    for coeff, mon in zip(coeffs, basis):
        term = coeff
        for g, e in zip(gens, mon):
            term *= g**e
        expr += term
    return _poly(expr, gens)

def _weighted_sos_from_gram(Q: sp.Matrix, block: dict):
    """
    Return a weighted SOS decomposition from an exact Gram matrix.
    """
    residual = sp.Matrix(Q)
    weighted_sos = []
    while residual != sp.zeros(*residual.shape):
        pivot = None
        for i in range(residual.rows):
            if residual[i, i] != 0:
                pivot = i
                break
        if pivot is None:
            break

        weight = sp.simplify(residual[pivot, pivot])
        vec = residual[:, pivot] / weight
        poly = _basis_poly([vec[i, 0] for i in range(vec.rows)], block["basis"], block["multiplier"].gens)
        weighted_sos.append((weight, poly))
        residual = (residual - weight * (vec * vec.T)).applyfunc(sp.simplify)

    result = {
        "multiplier": block["multiplier"],
        "sos_poly": _block_poly_from_gram(Q, block),
        "weighted_sos": weighted_sos,
    }
    if "multiplier_factors" in block:
        result["multiplier_factors"] = block["multiplier_factors"]
    if "multiplier_factor_indices" in block:
        result["multiplier_factor_indices"] = block["multiplier_factor_indices"]
    return result

def _exact_identity(target: sp.Poly, blocks: list[dict], exact_block_grams: list[sp.Matrix]):
    """
    Return the exact block identity and residual.
    """
    expr = 0
    for block, Q in zip(blocks, exact_block_grams):
        sigma = _block_poly_from_gram(Q, block)
        expr += block["multiplier"].as_expr() * sigma.as_expr()
    identity = _poly(sp.expand(expr), target.gens)
    residual = _poly(sp.expand(identity.as_expr() - target.as_expr()), target.gens)
    return identity, residual

def _locked_block_rows(compiled: dict, block_index: int, locked_coeffs: dict):
    """
    Return extra rows fixing a block's polynomial coefficients.
    """
    blocks = compiled["blocks"]
    total_cols = sum(len(block["upper_indices"]) for block in blocks) + len(compiled["param_symbols"])
    block = blocks[block_index]

    rows = []
    rhs = []
    for mon in sorted(set(block["rows_by_mon"]) | set(locked_coeffs)):
        row = [0] * total_cols
        sigma_row = block["rows_by_mon"].get(mon, [0] * len(block["upper_indices"]))
        for j, coeff in enumerate(sigma_row):
            row[block["slice"].start + j] = coeff
        rows.append(row)
        rhs.append(locked_coeffs.get(mon, 0))
    return rows, rhs

def _decorate_exact_certificate(result: dict):
    """
    Add algebraic certificate data to a successful exact result.
    """
    if "exact_block_grams" not in result:
        return result

    exact_certificate_blocks = [
        _weighted_sos_from_gram(Q, block)
        for Q, block in zip(result["exact_block_grams"], result["blocks"])
    ]
    result["exact_certificate_blocks"] = exact_certificate_blocks
    return result

# MAIN

def compile_sos_affine_system(
    p: sp.Poly,
    denom_degree_bound: int = 0,
    denom_template=None,
):
    """
    Compile the exact affine system for n = p * d, optionally with a denominator template.
    """
    if denom_degree_bound < 0:
        raise ValueError("denom_degree_bound must be nonnegative")
    if denom_degree_bound % 2 != 0:
        raise ValueError("denom_degree_bound must be even")

    gens = p.gens
    p_support = list(p.monoms())
    nvars = len(gens)

    template_poly = None
    template_coeffs = {}
    param_symbols = tuple()
    if denom_template is None:
        trace_normalization = True
        if denom_degree_bound == 0:
            den_basis = [(0,) * nvars]
            den_support = [(0,) * nvars]
        else:
            den_basis = monomial_basis_with_degree_bound(nvars, denom_degree_bound)
            den_support = sorted(_gram_rows_by_mon(den_basis, _upper_indices(len(den_basis))))
    else:
        template_poly, template_coeffs, param_symbols, trace_normalization = _template_data(
            denom_template, gens
        )
        den_support = list(template_coeffs)
        den_basis = monomial_basis_from_support(den_support)

    num_support = make_minkowski_sum(p_support, den_support)
    num_basis = monomial_basis_from_support(num_support)

    blocks = [
        {"name": "num", "multiplier": _poly(1, gens), "basis": num_basis},
        {"name": "den", "multiplier": _poly(-p, gens), "basis": den_basis},
    ]
    blocks = _prepare_certificate_blocks(blocks)

    extra_rows = []
    extra_rhs = []
    total_cols = sum(len(block["upper_indices"]) for block in blocks) + len(param_symbols)
    den_block = blocks[1]
    param_offset = total_cols - len(param_symbols)

    if denom_template is not None:
        zero_subs = {sym: 0 for sym in param_symbols}
        template_monoms = sorted(set(template_coeffs) | set(den_block["rows_by_mon"]))
        for mon in template_monoms:
            coeff_expr = template_coeffs.get(mon, sp.Integer(0))
            row = [0] * total_cols
            sigma_row = den_block["rows_by_mon"].get(mon, [0] * len(den_block["upper_indices"]))
            for j, coeff in enumerate(sigma_row):
                row[den_block["slice"].start + j] = coeff
            for j, sym in enumerate(param_symbols):
                row[param_offset + j] -= sp.expand(coeff_expr).coeff(sym)
            extra_rows.append(row)
            extra_rhs.append(sp.expand(coeff_expr).subs(zero_subs))

    if trace_normalization:
        row = [0] * total_cols
        for j, (u, v) in enumerate(den_block["upper_indices"]):
            if u == v:
                row[den_block["slice"].start + j] = 1
        extra_rows.append(row)
        extra_rhs.append(1)

    compiled = _compile_certificate_affine_system(
        _poly(0, gens),
        blocks,
        param_symbols=param_symbols,
        extra_rows=extra_rows,
        extra_rhs=extra_rhs,
    )
    compiled.update({
        "kind": "sos",
        "template_poly": template_poly,
        "num_basis": num_basis,
        "den_basis": den_basis,
        "num_upper_indices": blocks[0]["upper_indices"],
        "den_upper_indices": blocks[1]["upper_indices"],
        "den_rows_by_mon": den_block["rows_by_mon"],
        "lock_block_index": 1 if len(den_basis) > 1 else None,
    })
    if denom_degree_bound == 0 and denom_template is None:
        compiled["basis"] = num_basis
        compiled["upper_indices"] = blocks[0]["upper_indices"]
    return compiled

def numeric_certificate_solution(compiled: dict):
    """
    Solve a certificate SDP numerically.
    """
    A = np.asarray(compiled["A"].tolist(), dtype=float)
    b = np.asarray(list(compiled["b"]), dtype=float)

    block_vars = []
    pieces = []
    for block in compiled["blocks"]:
        Q = cp.Variable((len(block["basis"]), len(block["basis"])), PSD=True)
        block_vars.append(Q)
        pieces += [Q[i, j] for i, j in block["upper_indices"]]
    params = None
    if compiled["param_symbols"]:
        params = cp.Variable(len(compiled["param_symbols"]))
        pieces += list(params)

    q = cp.hstack(pieces)
    prob = cp.Problem(cp.Minimize(0.0), [A @ q == b])
    prob.solve(solver=cp.CLARABEL, verbose=False)

    return {
        **compiled,
        "status": prob.status,
        "block_grams": [Q.value for Q in block_vars],
        "param_values": {
            sym: float(params.value[idx]) for idx, sym in enumerate(compiled["param_symbols"])
        } if params is not None else {},
    }

def gauss_newton_refine_certificate_solution(sol: dict, max_iters: int = 8, tol: float = 1e-12):
    """
    Refine a numeric certificate solution in factor space.
    """
    if any(Q is None for Q in sol["block_grams"]):
        return {**sol, "residual_norm": float("inf")}

    A = np.asarray(sol["A"].tolist(), dtype=float)
    b = np.asarray(list(sol["b"]), dtype=float)
    param_values = np.asarray(
        [sol["param_values"][sym] for sym in sol["param_symbols"]],
        dtype=float,
    ) if sol["param_symbols"] else np.array([], dtype=float)

    factors = [_gram_factor(Q) for Q in sol["block_grams"]]

    def q_of(factors):
        parts = [
            _upper_vec(C.T @ C, block["upper_indices"])
            for C, block in zip(factors, sol["blocks"])
        ]
        if len(param_values):
            parts.append(param_values)
        return np.concatenate(parts)

    q = q_of(factors)
    residual = A @ q - b

    for _ in range(max_iters):
        if np.linalg.norm(residual) <= tol:
            break

        J_parts = [
            _factor_jacobian(A[:, block["slice"]], C, block["upper_indices"])
            for C, block in zip(factors, sol["blocks"])
        ]
        J = np.hstack(J_parts)

        delta, *_ = np.linalg.lstsq(J, -residual, rcond=None)
        delta_factors = []
        start = 0
        for C in factors:
            stop = start + C.size
            delta_factors.append(delta[start:stop].reshape(C.shape))
            start = stop

        improved = False
        for step in [1.0, 0.5, 0.25, 0.125]:
            trial_factors = [C + step * dC for C, dC in zip(factors, delta_factors)]
            q_trial = q_of(trial_factors)
            residual_trial = A @ q_trial - b
            if np.linalg.norm(residual_trial) < np.linalg.norm(residual):
                factors = trial_factors
                q = q_trial
                residual = residual_trial
                improved = True
                break
        if not improved:
            break

    return {
        **sol,
        "block_grams": [C.T @ C for C in factors],
        "residual_norm": float(np.linalg.norm(residual)),
    }

def _exactify_with_locked_block(
    refined: dict,
    block_index: int,
    max_denominators: tuple[int, ...] | None,
    gn_max_iters: int,
):
    """
    Try exactification after locking one block polynomial first.
    """
    q_numeric = _q_numeric(refined)
    block = refined["blocks"][block_index]
    q_block = q_numeric[block["slice"]]
    block_coeffs = _block_coeffs(q_block, block["rows_by_mon"])

    for max_den in (max_denominators if max_denominators is not None else _denominator_sequence()):
        if max_den is None:
            locked_coeffs = {
                mon: sp.Rational(coeff)
                for mon, coeff in block_coeffs.items()
            }
        else:
            locked_coeffs = {
                mon: sp.Rational(Fraction(float(coeff)).limit_denominator(max_den))
                for mon, coeff in block_coeffs.items()
            }
        try:
            extra_rows, extra_rhs = _locked_block_rows(refined, block_index, locked_coeffs)
            A_locked = sp.Matrix(list(refined["A"].tolist()) + extra_rows)
            b_locked = sp.Matrix(list(refined["b"]) + extra_rhs)
            A_locked, b_locked = _reduce_affine_system(A_locked, b_locked)
        except ValueError:
            continue

        if max_den is None:
            q0 = sp.Matrix([sp.Rational(v) for v in q_numeric])
        else:
            q0 = sp.Matrix([
                sp.Rational(Fraction(float(v)).limit_denominator(max_den))
                for v in q_numeric
            ])
        q_exact = _project_to_affine_space_exact(q0, A_locked, b_locked)
        exact_block_grams = _exact_block_grams(q_exact, refined["blocks"])
        if A_locked * q_exact != b_locked or not _exact_psd(exact_block_grams[block_index]):
            continue

        remaining_blocks = [b for j, b in enumerate(refined["blocks"]) if j != block_index]
        if not remaining_blocks:
            if all(_exact_psd(Q) for Q in exact_block_grams):
                identity, residual = _exact_identity(refined["target"], refined["blocks"], exact_block_grams)
                return _decorate_exact_certificate({
                    **refined,
                    "success": True,
                    "exact_block_grams": exact_block_grams,
                    "exact_identity": identity,
                    "exact_residual": residual,
                    "max_denominator": max_den,
                })
            continue

        locked_poly = _poly(_poly_from_coeffs(locked_coeffs, refined["gens"]), refined["gens"])
        target_reduced = _poly(
            sp.expand(
                refined["target"].as_expr()
                - refined["blocks"][block_index]["multiplier"].as_expr() * locked_poly.as_expr()
            ),
            refined["gens"],
        )
        reduced_compiled = _compile_certificate_affine_system(target_reduced, remaining_blocks)
        reduced_sol = {
            **reduced_compiled,
            "status": refined["status"],
            "block_grams": [Q for j, Q in enumerate(refined["block_grams"]) if j != block_index],
            "param_values": {},
            "lock_block_index": None,
        }
        reduced_result = exactify_certificate_solution(
            reduced_sol,
            max_denominators=max_denominators,
            gn_max_iters=gn_max_iters,
        )
        if not reduced_result["success"]:
            continue

        locked_exact_gram = exact_block_grams[block_index]
        exact_block_grams = []
        k = 0
        for j in range(len(refined["blocks"])):
            if j == block_index:
                exact_block_grams.append(locked_exact_gram)
            else:
                exact_block_grams.append(reduced_result["exact_block_grams"][k])
                k += 1
        identity, residual = _exact_identity(refined["target"], refined["blocks"], exact_block_grams)
        result = _decorate_exact_certificate({
            **refined,
            "success": True,
            "exact_block_grams": exact_block_grams,
            "exact_identity": identity,
            "exact_residual": residual,
            "max_denominator": reduced_result["max_denominator"],
        })
        if refined["param_symbols"]:
            param_start = sum(len(b["upper_indices"]) for b in refined["blocks"])
            result["exact_param_values"] = {
                sym: q_exact[param_start + idx, 0]
                for idx, sym in enumerate(refined["param_symbols"])
            }
        return result

    return None

def _try_exactify_at_denominator(refined, q_numeric, max_den):
    """Try exactification at a given max_denominator. Returns result dict or None."""
    if max_den is None:
        q0 = sp.Matrix([sp.Rational(v) for v in q_numeric])
    else:
        q0 = sp.Matrix([
            sp.Rational(Fraction(float(v)).limit_denominator(max_den))
            for v in q_numeric
        ])
    q_exact = _project_to_affine_space_exact(q0, refined["A"], refined["b"])
    exact_block_grams = _exact_block_grams(q_exact, refined["blocks"])
    if refined["A"] * q_exact != refined["b"]:
        return None
    if not all(_exact_psd(Q) for Q in exact_block_grams):
        return None

    identity, residual = _exact_identity(refined["target"], refined["blocks"], exact_block_grams)
    result = _decorate_exact_certificate({
        **refined,
        "success": True,
        "exact_block_grams": exact_block_grams,
        "exact_identity": identity,
        "exact_residual": residual,
        "exact_vector": q_exact,
        "max_denominator": max_den,
    })
    if refined["param_symbols"]:
        param_start = sum(len(block["upper_indices"]) for block in refined["blocks"])
        result["exact_param_values"] = {
            sym: q_exact[param_start + idx, 0]
            for idx, sym in enumerate(refined["param_symbols"])
        }
    return result


def _denominator_sequence(max_cap=10**6):
    """Yield 1, 2, 4, 8, ..., max_cap, then None (no limit)."""
    d = 1
    while d <= max_cap:
        yield d
        d *= 2
    yield None


def exactify_certificate_solution(
    sol: dict,
    max_denominators: tuple[int, ...] | None = None,
    gn_max_iters: int = 8,
):
    """
    Exactify a numeric certificate solution.

    1. Refines the numeric solution with Gauss-Newton in factor space.
    2. For each denominator limit (1, 2, 4, 8, ..., then unlimited),
       rounds entries to rationals, projects onto the affine constraint
       space, and checks exact PSD of each Gram block via LDL.
    3. If all denominators fail, returns with ``success=False``.
    """
    if any(Q is None for Q in sol["block_grams"]):
        return {**sol, "success": False}

    refined = gauss_newton_refine_certificate_solution(sol, max_iters=gn_max_iters)

    lock_block_index = refined.get("lock_block_index")
    if lock_block_index is not None:
        locked = _exactify_with_locked_block(
            refined,
            lock_block_index,
            max_denominators=max_denominators,
            gn_max_iters=gn_max_iters,
        )
        if locked is not None:
            return locked

    q_numeric = _q_numeric(refined)
    for max_den in (max_denominators if max_denominators is not None else _denominator_sequence()):
        result = _try_exactify_at_denominator(refined, q_numeric, max_den)
        if result is not None:
            return result

    return {**refined, "success": False}

def _decorate_sos_result(result: dict):
    """
    Add the usual SOS aliases to a result dictionary.
    """
    result["num_basis"] = result["blocks"][0]["basis"]
    result["den_basis"] = result["blocks"][1]["basis"]
    result["num_upper_indices"] = result["blocks"][0]["upper_indices"]
    result["den_upper_indices"] = result["blocks"][1]["upper_indices"]
    result["den_rows_by_mon"] = result["blocks"][1]["rows_by_mon"]
    if len(result["blocks"][1]["basis"]) == 1:
        result["basis"] = result["blocks"][0]["basis"]
        result["upper_indices"] = result["blocks"][0]["upper_indices"]
    if "block_grams" in result:
        result["num_gram"] = result["block_grams"][0]
        result["den_gram"] = result["block_grams"][1]
        if len(result["blocks"][1]["basis"]) == 1:
            result["gram"] = result["block_grams"][0]
    if "exact_block_grams" in result:
        result["exact_num_gram"] = result["exact_block_grams"][0]
        result["exact_den_gram"] = result["exact_block_grams"][1]
        result["exact_num_poly"] = result["exact_certificate_blocks"][0]["sos_poly"]
        result["exact_den_poly"] = result["exact_certificate_blocks"][1]["sos_poly"]
        result["exact_num_sos"] = result["exact_certificate_blocks"][0]["weighted_sos"]
        result["exact_den_sos"] = result["exact_certificate_blocks"][1]["weighted_sos"]
        coeff_witness = _find_nonzero_coeff_witness(result["exact_den_poly"])
        if coeff_witness is not None:
            result["exact_den_nonzero_coeff_witness"] = coeff_witness
        witness = _find_nonzero_eval_witness(result["exact_den_poly"])
        if witness is not None:
            result["exact_den_nonzero_witness"] = witness
        if len(result["blocks"][1]["basis"]) == 1:
            result["exact_gram"] = result["exact_block_grams"][0]
            result["exact_sos"] = result["exact_certificate_blocks"][0]["weighted_sos"]
    return result

def numeric_sos_solution(p: sp.Poly, denom_degree_bound: int = 0, denom_template=None):
    """
    Solve the SOS SDP numerically, optionally with a denominator template.
    """
    return _decorate_sos_result(
        numeric_certificate_solution(
            compile_sos_affine_system(
                p,
                denom_degree_bound=denom_degree_bound,
                denom_template=denom_template,
            )
        )
    )

def gauss_newton_refine_sos_solution(sol: dict, max_iters: int = 8, tol: float = 1e-12):
    """
    Refine a numeric SOS solution in factor space.
    """
    return _decorate_sos_result(
        gauss_newton_refine_certificate_solution(sol, max_iters=max_iters, tol=tol)
    )

def exactify_sos_solution(
    sol: dict,
    max_denominators: tuple[int, ...] | None = None,
    gn_max_iters: int = 8,
):
    """
    Run GN, round to rationals, then affine-project exactly.
    Returns exact Gram data and weighted SOS data.
    """
    return _decorate_sos_result(
        exactify_certificate_solution(
            sol,
            max_denominators=max_denominators,
            gn_max_iters=gn_max_iters,
        )
    )

def _sos_diagnostics(result: dict):
    """Diagnostics for failed sos_decomp: denominator and numerator analysis."""
    diag = {"status": result.get("status")}
    has_denom = len(result.get("den_basis", [])) > 1

    if result.get("status") == "infeasible":
        if not has_denom:
            diag["suggestion"] = "not SOS — try adding a denominator with denom_degree_bound=2"
        else:
            diag["suggestion"] = "infeasible — try a higher denom_degree_bound or a specific denom_template"
        return diag

    # Optimal but exactification failed — analyze blocks
    for key, block_idx, label in [("numerator", 0, "num"), ("denominator", 1, "den")]:
        Q = result.get("block_grams", [None, None])[block_idx]
        if Q is None or Q.ndim < 2:
            continue
        basis = result.get(f"{label}_basis", [])
        evals, evecs = np.linalg.eigh(Q)
        rank = int(np.sum(evals > 1e-6))
        active_mask = np.zeros(len(basis), dtype=bool)
        for i in range(len(evals)):
            if evals[i] > 1e-6:
                active_mask |= (np.abs(evecs[:, i]) > 1e-4)
        diag[key] = {
            "rank": rank,
            "size": Q.shape[0],
            "active_monomials": [basis[i] for i in range(len(basis)) if active_mask[i]],
            "inactive_monomials": [basis[i] for i in range(len(basis)) if not active_mask[i]],
        }

    # Generate suggestion
    den_info = diag.get("denominator", {})
    num_info = diag.get("numerator", {})
    if den_info.get("inactive_monomials"):
        gens = result.get("gens", [])
        active = den_info["active_monomials"]
        terms = []
        for mon in active:
            parts = [f"{g}**{e}" if e > 1 else str(g) for g, e in zip(gens, mon) if e > 0]
            terms.append("*".join(parts) if parts else "1")
        diag["suggestion"] = (
            f"denominator is rank-deficient ({den_info['rank']}/{den_info['size']}). "
            f"Try a denom_template using only active monomials: {', '.join(terms)}"
        )
    elif num_info.get("rank", 0) < num_info.get("size", 0) and has_denom:
        diag["suggestion"] = (
            f"numerator is rank-deficient ({num_info['rank']}/{num_info['size']}). "
            f"The polynomial may be SOS without a denominator — try denom_degree_bound=0"
        )
    return diag


def sos_decomp(p: sp.Poly, denom_degree_bound: int = 0, denom_template=None):
    """
    Prove that a polynomial p is globally nonneg by finding an exact SOS certificate.

    When denom_degree_bound == 0 (default), finds SOS polynomials s_i such that:
        p = w_1 * s_1^2 + w_2 * s_2^2 + ...    (w_i >= 0)

    When denom_degree_bound > 0, finds an SOS denominator d and SOS numerator n such that:
        d * p = n,  d != 0,  d >= 0,  n >= 0
    This handles polynomials like Motzkin's that are nonneg but not themselves SOS.

    On failure, the result includes ``diagnostics`` with rank info for each block,
    active/inactive denominator monomials, and a suggestion for what to try next.

    Args:
        p: the polynomial to decompose (as a sympy Poly).
        denom_degree_bound: maximum degree of the SOS denominator polynomial.
            Must be even. 0 means no denominator (pure SOS). 2 is usually enough.
        denom_template: optional explicit denominator template (a sympy expression
            with free parameters). Overrides denom_degree_bound if provided.
    """
    result = exactify_sos_solution(
        numeric_sos_solution(
            p,
            denom_degree_bound=denom_degree_bound,
            denom_template=denom_template,
        )
    )
    if not result["success"]:
        result["diagnostics"] = _sos_diagnostics(result)
    return result


def _block_diagnostics(result: dict):
    """Per-block size/rank/eigenvalue diagnostics for failed exactification."""
    diags = []
    for i, Q in enumerate(result.get("block_grams", [])):
        if Q is None or Q.ndim < 2:
            continue
        evals = np.linalg.eigvalsh(Q)
        diags.append({
            "block": i,
            "size": Q.shape[0],
            "numeric_rank": int(np.sum(evals > 1e-6)),
            "min_eigenvalue": float(evals[0]),
        })
    return diags

def _normalize_positivstellensatz_input(constraints, target):
    """
    Normalize the target and constraints for Putinar and Schmudgen.
    """
    constraints = list(constraints)
    gens = _common_gens([target] + constraints)
    return _poly(target, gens), [_poly(g, gens) for g in constraints]

def putinar(target, constraints, degree_bound: int, block_bases: dict[int, list] | None = None):
    """
    Prove that target >= 0 on the semialgebraic set {x : g_1(x) >= 0, ..., g_m(x) >= 0}
    using Putinar's Positivstellensatz.

    Finds SOS polynomials sigma_0, sigma_1, ..., sigma_m such that:
        target = sigma_0 + g_1 * sigma_1 + ... + g_m * sigma_m

    Blocks are indexed as: 0 = free SOS (multiplier 1), 1 = g_1, ..., m = g_m.

    Args:
        target: polynomial to prove nonneg (sympy expression or Poly).
        constraints: list of g_i polynomials defining the feasible set.
        degree_bound: maximum (even) degree of each SOS multiplier sigma_i.
            Each sigma_i is a sum of squares of polynomials whose monomials
            have degree up to degree_bound // 2.
        block_bases: optional dict mapping block index to a monomial basis list,
            overriding the default full-degree basis for that block. Useful when
            exactification fails due to rank-deficient Gram matrices: run once
            without ``block_bases`` and check ``block_diagnostics`` in the
            returned dict to find blocks whose ``numeric_rank`` is less than
            ``size``, then re-run with a smaller basis for those blocks
            (e.g. ``{3: monomial_basis_with_degree_bound(n, 4)}`` to give
            block 3 a degree-4 basis instead of the default).
    """
    if degree_bound < 0 or degree_bound % 2 != 0:
        raise ValueError("degree_bound must be a nonnegative even integer")
    target, constraints = _normalize_positivstellensatz_input(constraints, target)
    gens = target.gens
    default_basis = monomial_basis_with_degree_bound(len(gens), degree_bound)
    multipliers = [_poly(1, gens)] + constraints
    blocks = []
    for i, h in enumerate(multipliers):
        basis = block_bases[i] if block_bases and i in block_bases else default_basis
        blocks.append({
            "name": f"sigma_{i}",
            "multiplier": h,
            "multiplier_factors": [] if i == 0 else [h],
            "multiplier_factor_indices": [] if i == 0 else [i - 1],
            "basis": basis,
        })
    compiled = _compile_certificate_affine_system(target, blocks)
    compiled["kind"] = "putinar"
    result = exactify_certificate_solution(numeric_certificate_solution(compiled))
    if not result["success"]:
        result["block_diagnostics"] = _block_diagnostics(result)
    return result

def putinar_empty(constraints, degree_bound: int, block_bases: dict[int, list] | None = None):
    """
    Prove that {x : g_1(x) >= 0, ..., g_m(x) >= 0} is empty using Putinar's
    Positivstellensatz. Equivalent to putinar(-1, constraints, degree_bound).

    See :func:`putinar` for the meaning of ``block_bases``.
    """
    return putinar(-1, constraints, degree_bound, block_bases=block_bases)

def schmudgen(target, constraints, degree_bound: int, block_bases: dict[int, list] | None = None):
    """
    Prove that target >= 0 on the semialgebraic set {x : g_1(x) >= 0, ..., g_m(x) >= 0}
    using Schmudgen's Positivstellensatz.

    Finds SOS polynomials sigma_S for each subset S of constraints such that:
        target = sigma_0 + sum_{i} g_i * sigma_{i}
                         + sum_{i<j} g_i * g_j * sigma_{i,j} + ...

    Schmudgen uses all 2^m products of subsets of constraints as multipliers,
    while Putinar uses only individual constraints. This makes Schmudgen more
    powerful (works on any compact set) but the SDP grows exponentially in the
    number of constraints.

    Blocks are indexed as: 0 = free SOS (multiplier 1), then subsets of
    constraints in lexicographic order by size: {0}, {1}, ..., {0,1}, {0,2}, ...

    Args:
        target: polynomial to prove nonneg (sympy expression or Poly).
        constraints: list of g_i polynomials defining the feasible set.
        degree_bound: maximum (even) degree of each SOS multiplier sigma_S.
            Each sigma_S is a sum of squares of polynomials whose monomials
            have degree up to degree_bound // 2.
        block_bases: optional dict mapping block index to a monomial basis list,
            overriding the default full-degree basis for that block. Useful when
            exactification fails due to rank-deficient Gram matrices: run once
            without ``block_bases`` and check ``block_diagnostics`` in the
            returned dict to find blocks whose ``numeric_rank`` is less than
            ``size``, then re-run with a smaller basis for those blocks
            (e.g. ``{3: monomial_basis_with_degree_bound(n, 4)}`` to give
            block 3 a degree-4 basis instead of the default).
    """
    if degree_bound < 0 or degree_bound % 2 != 0:
        raise ValueError("degree_bound must be a nonnegative even integer")
    target, gs = _normalize_positivstellensatz_input(constraints, target)
    gens = target.gens
    default_basis = monomial_basis_with_degree_bound(len(gens), degree_bound)
    multipliers = [_poly(1, gens)]
    multiplier_factors = [[]]
    multiplier_factor_indices = [[]]
    for r in range(1, len(gs) + 1):
        for indices in combinations(range(len(gs)), r):
            subset = [gs[i] for i in indices]
            expr = 1
            for g in subset:
                expr *= g.as_expr()
            multipliers.append(_poly(expr, gens))
            multiplier_factors.append(list(subset))
            multiplier_factor_indices.append(list(indices))
    blocks = []
    for i, h in enumerate(multipliers):
        basis = block_bases[i] if block_bases and i in block_bases else default_basis
        blocks.append({
            "name": f"sigma_{i}",
            "multiplier": h,
            "multiplier_factors": multiplier_factors[i],
            "multiplier_factor_indices": multiplier_factor_indices[i],
            "basis": basis,
        })
    compiled = _compile_certificate_affine_system(target, blocks)
    compiled["kind"] = "schmudgen"
    result = exactify_certificate_solution(numeric_certificate_solution(compiled))
    if not result["success"]:
        result["block_diagnostics"] = _block_diagnostics(result)
    return result

def schmudgen_empty(constraints, degree_bound: int, block_bases: dict[int, list] | None = None):
    """
    Prove that {x : g_1(x) >= 0, ..., g_m(x) >= 0} is empty using Schmudgen's
    Positivstellensatz. Equivalent to schmudgen(-1, constraints, degree_bound).

    See :func:`schmudgen` for the meaning of ``block_bases``.
    """
    return schmudgen(-1, constraints, degree_bound, block_bases=block_bases)

# CLI

def _parse_vars(vars_text: str | None):
    """
    Parse a whitespace-separated variable list.
    """
    if vars_text is None:
        return None
    syms = sp.symbols(vars_text)
    return (syms,) if isinstance(syms, sp.Symbol) else tuple(syms)

def _parse_expr_list(exprs_text: str):
    """
    Parse a comma-delimited list of SymPy expressions.
    """
    return [sp.sympify(expr.strip()) for expr in exprs_text.split(",") if expr.strip()]

def _serialize_poly(poly: sp.Poly):
    """
    Serialize a polynomial for JSON output.
    """
    return {
        "expr": str(poly.as_expr()),
        "gens": [str(g) for g in poly.gens],
    }

def _serialize_weighted_sos(weighted_sos):
    """
    Serialize a weighted SOS list for JSON output.
    """
    return [
        {
            "weight": str(weight),
            "poly": _serialize_poly(poly),
        }
        for weight, poly in weighted_sos
    ]

def _serialize_certificate_blocks(blocks):
    """
    Serialize certificate blocks for JSON output.
    """
    return [
        {
            "multiplier": _serialize_poly(block["multiplier"]),
            "sos_poly": _serialize_poly(block["sos_poly"]),
            "multiplier_factors": [
                _serialize_poly(poly) for poly in block.get("multiplier_factors", [])
            ],
            "multiplier_factor_indices": block.get("multiplier_factor_indices", []),
            "weighted_sos": _serialize_weighted_sos(block["weighted_sos"]),
        }
        for block in blocks
    ]

def _find_nonzero_eval_witness(poly: sp.Poly):
    """
    Find a small rational point where poly evaluates to a nonzero value.
    """
    search_values = [0, 1, -1, 2, -2, 3, -3]
    for values in product(search_values, repeat=len(poly.gens)):
        value = sp.simplify(poly.eval(dict(zip(poly.gens, values))))
        if value != 0:
            return {
                "values": [str(sp.Rational(v)) for v in values],
                "value": str(sp.Rational(value)),
            }
    return None

def _find_nonzero_coeff_witness(poly: sp.Poly):
    """
    Return a low-degree monomial with nonzero coefficient.
    The witness is sorted first by total degree, then lexicographically.
    """
    nonzero_terms = sorted(
        ((mon, coeff) for mon, coeff in poly.as_dict().items() if coeff != 0),
        key=lambda item: (sum(item[0]), item[0]),
    )
    if not nonzero_terms:
        return None
    mon, coeff = nonzero_terms[0]
    return {
        "exponents": list(mon),
        "coeff": str(sp.Rational(coeff)),
    }

def _serialize_result(result: dict):
    """
    Serialize a certificate result for JSON output.
    """
    payload = {
        "kind": result.get("kind"),
        "success": result["success"],
        "status": result.get("status"),
        "max_denominator": result.get("max_denominator"),
    }
    if "exact_identity" in result:
        payload["exact_identity"] = _serialize_poly(result["exact_identity"])
    if "exact_residual" in result:
        payload["exact_residual"] = _serialize_poly(result["exact_residual"])
    if "exact_certificate_blocks" in result:
        payload["exact_certificate_blocks"] = _serialize_certificate_blocks(result["exact_certificate_blocks"])
    if "exact_num_poly" in result:
        payload["exact_num_poly"] = _serialize_poly(result["exact_num_poly"])
    if "exact_den_poly" in result:
        payload["exact_den_poly"] = _serialize_poly(result["exact_den_poly"])
    if "exact_num_sos" in result:
        payload["exact_num_sos"] = _serialize_weighted_sos(result["exact_num_sos"])
    if "exact_den_sos" in result:
        payload["exact_den_sos"] = _serialize_weighted_sos(result["exact_den_sos"])
    if "exact_den_nonzero_witness" in result:
        payload["exact_den_nonzero_witness"] = result["exact_den_nonzero_witness"]
    if "exact_den_nonzero_coeff_witness" in result:
        payload["exact_den_nonzero_coeff_witness"] = result["exact_den_nonzero_coeff_witness"]
    if "exact_sos" in result:
        payload["exact_sos"] = _serialize_weighted_sos(result["exact_sos"])
    if "exact_param_values" in result:
        payload["exact_param_values"] = {
            str(sym): str(value)
            for sym, value in result["exact_param_values"].items()
        }
    if "block_diagnostics" in result:
        payload["block_diagnostics"] = result["block_diagnostics"]
    if "diagnostics" in result:
        payload["diagnostics"] = result["diagnostics"]
    # Surface a top-level suggestion string for Lean tactic error messages
    if not result["success"]:
        suggestion = None
        if "diagnostics" in result:
            suggestion = result["diagnostics"].get("suggestion")
        elif "block_diagnostics" in result:
            deficient = [
                b for b in result["block_diagnostics"]
                if b["numeric_rank"] < b["size"]
            ]
            if deficient:
                n_vars = len(result.get("gens", []))
                bb_parts = []
                for b in deficient:
                    # find smallest degree d such that C(n+d,d) >= numeric_rank
                    from math import comb
                    d = 0
                    while comb(n_vars + d, d) < b["numeric_rank"]:
                        d += 1
                    bb_parts.append(f"{b['block']}:{d}")
                bb_str = ",".join(bb_parts)
                suggestion = f'try block_bases := "{bb_str}"'
        if suggestion:
            payload["suggestion"] = suggestion
    return payload

def _parse_block_bases(s, n_vars):
    """Parse block-bases string like '3:4,1:2' into {3: basis_deg4, 1: basis_deg2}."""
    if s is None:
        return None
    result = {}
    for part in s.split(","):
        block_str, deg_str = part.strip().split(":")
        result[int(block_str)] = monomial_basis_with_degree_bound(n_vars, int(deg_str))
    return result

def _run_cli(args):
    """
    Run one CLI command.
    """
    if args.command == "sos_decomp":
        poly_expr = sp.sympify(args.poly)
        template_expr = sp.sympify(args.denom_template) if args.denom_template is not None else None
        gens = _parse_vars(args.vars)
        if gens is None:
            gens = _common_gens([poly_expr])
        poly = _poly(poly_expr, gens)
        denom_template = _poly(template_expr, gens) if template_expr is not None else None
        if denom_template is not None:
            template_vars = set(template_expr.free_symbols) & set(gens)
            if not template_vars and gens:
                names = ", ".join(str(g) for g in gens)
                raise ValueError(
                    f"denom_template shares no variables with the polynomial (expected: {names})"
                )
        result = sos_decomp(
            poly,
            denom_degree_bound=args.denom_degree_bound,
            denom_template=denom_template,
        )
    elif args.command == "putinar":
        target = sp.sympify(args.poly)
        constraints = _parse_expr_list(args.constraints)
        gens = _parse_vars(args.vars)
        if gens is None:
            gens = _common_gens([target] + constraints)
        block_bases = _parse_block_bases(getattr(args, 'block_bases', None), len(gens))
        target = _poly(target, gens)
        constraints = [_poly(g, gens) for g in constraints]
        result = putinar(target, constraints, degree_bound=args.degree_bound, block_bases=block_bases)
    else:
        target = sp.sympify(args.poly)
        constraints = _parse_expr_list(args.constraints)
        gens = _parse_vars(args.vars)
        if gens is None:
            gens = _common_gens([target] + constraints)
        block_bases = _parse_block_bases(getattr(args, 'block_bases', None), len(gens))
        target = _poly(target, gens)
        constraints = [_poly(g, gens) for g in constraints]
        result = schmudgen(target, constraints, degree_bound=args.degree_bound, block_bases=block_bases)

    payload = _serialize_result(result)
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.out is None:
        print(text)
    else:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    return 0

def _main(argv=None):
    """
    Run the command-line interface.
    """
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    sos_parser = subparsers.add_parser("sos_decomp")
    sos_parser.add_argument("--poly", required=True)
    sos_parser.add_argument("--vars")
    sos_parser.add_argument("--denom-degree-bound", type=int, default=0)
    sos_parser.add_argument("--denom-template")
    sos_parser.add_argument("--out")

    putinar_parser = subparsers.add_parser("putinar")
    putinar_parser.add_argument("--poly", default="-1")
    putinar_parser.add_argument("--constraints", required=True)
    putinar_parser.add_argument("--vars")
    putinar_parser.add_argument("--degree-bound", type=int, required=True)
    putinar_parser.add_argument("--block-bases", help="per-block basis overrides, e.g. '3:4' to use degree-4 basis for block 3")
    putinar_parser.add_argument("--out")

    schmudgen_parser = subparsers.add_parser("schmudgen")
    schmudgen_parser.add_argument("--poly", default="-1")
    schmudgen_parser.add_argument("--constraints", required=True)
    schmudgen_parser.add_argument("--vars")
    schmudgen_parser.add_argument("--degree-bound", type=int, required=True)
    schmudgen_parser.add_argument("--block-bases", help="per-block basis overrides, e.g. '3:4' to use degree-4 basis for block 3")
    schmudgen_parser.add_argument("--out")

    args = parser.parse_args(argv)
    try:
        return _run_cli(args)
    except Exception as exc:
        print(f"{type(exc).__name__}: {exc}", file=sys.stderr)
        return 1

if __name__ == "__main__":
    raise SystemExit(_main())
