# Sostactic

This is a collection of Lean4 tactics for proving polynomial inequalities via _sum-of-squares (SOS) decompositions_, powered by a Python backend.

These tactics are significantly more powerful than `nlinarith` and `positivity` -- i.e., they can prove inequalities they cannot.

## Quick Example

```lean
import Sostactic

-- Motzkin polynomial: nonneg but not a sum of squares
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (degree := 2)

-- Nonneg on a semialgebraic set: 4x³ - 3x + 1 ≥ 0 on [0, 1]
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (degree := 2)

-- Prove a set is empty: {x ≥ 0, x ≤ -1}
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ -x - 1) : False := by
  putinar_empty (degree := 0)
```

## Setup

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager)
- Python 3.10+

### 1. Add the dependency

In your project's `lakefile.lean`:

```lean
require sostactic from git
  "https://github.com/mmaaz-git/sostactic.git" @ "main"
```

Then fetch and build:

```bash
lake update sostactic
lake build
```

### 2. Set up the Python environment

Create a virtual environment in your project root and install the dependencies:

```bash
python3 -m venv .venv
.venv/bin/pip install -r .lake/packages/Sostactic/python/requirements.txt
```

That's it. Sostactic auto-discovers `.venv/bin/python3` in your project root.

> **Tip:** Add `.venv/` to your `.gitignore`.

### Advanced: custom Python path

If your Python lives elsewhere, set the `SOSTACTIC_PYTHON` environment variable:

```bash
export SOSTACTIC_PYTHON=/path/to/your/python3
```

## Tactics

### `sos_decomp` — Global nonnegativity

Proves that a polynomial `f` is nonnegative globally by finding an SOS decomposition, optionally with a denominator to decompose it into a ratio of SOS polynomials. By Artin's theorem, any globally nonnegative polynomial can be decomposed into a ratio of SOS.

```lean
-- plain SOS
example (x y : ℝ) : 0 ≤ x^2 + y^2 := by sos_decomp

-- with denominator search (degree bound for the denominator)
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (degree := 2)

-- with explicit denominator template
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (degree := 2) (denom_template := "a*x^2 + b*y^2 + c*z^2")

-- also handles a ≤ b and a ≥ b goals
example (x y : ℝ) : 2 * x * y ≤ x^2 + y^2 := by sos_decomp
```

### `putinar_decomp` / `schmudgen_decomp` — Nonnegativity on semialgebraic sets

Proves `0 ≤ f` given hypotheses of the form `0 ≤ gᵢ`, using Putinar's or Schmüdgen's Positivstellensatz.

```lean
-- Putinar: requires Archimedean (compact) constraints
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (degree := 2)

-- Schmüdgen: requires compact constraints, uses products of gᵢ
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (degree := 0)
```

### `putinar_empty` / `schmudgen_empty` — Emptiness of semialgebraic sets

Proves `False` from contradictory hypotheses `0 ≤ gᵢ`, showing the feasible set is empty.

```lean
-- {x ≥ 0, x ≤ -1} is empty
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ -x - 1) : False := by
  putinar_empty (degree := 0)

-- disjoint disks
example (x y : ℝ) (h1 : 0 ≤ 1 - x^2 - y^2) (h2 : 0 ≤ x^2 + y^2 - 2) : False := by
  schmudgen_empty (degree := 2)
```

### Common parameters

| Parameter | Description |
|-----------|-------------|
| `degree := n` | Degree bound for the SOS multipliers / denominator |
| `denom_template := "..."` | Explicit denominator template (for `sos_decomp`) |
| `block_bases := "1:2,2:3"` | Block structure hint for the SDP (block:degree pairs) |
| `cert := "path.json"` | Load a pre-generated certificate from file |

## Certificate Import

The SDP solver can be slow for large problems. You can pre-generate certificates and load them from JSON files, so the solver doesn't re-run on every file reload:

```lean
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (cert := "certs/motzkin.json")
```

Lean still independently verifies the certificate — the JSON file is untrusted.

## How It Works

1. The tactic extracts the polynomial inequality from the Lean goal
2. A Python backend formulates and solves a semidefinite program (SDP) using CVXPY + Clarabel
3. The backend returns an exact rational certificate (SOS decomposition or Positivstellensatz certificate)
4. The tactic reconstructs the proof in Lean using `ring_nf` and `positivity`, which Lean's kernel verifies

The SDP solution is numerical, but the returned certificate is exact — Lean verifies it independently, so the proof is fully rigorous.

## Dependencies

**Lean:** [Mathlib](https://github.com/leanprover-community/mathlib4) (multivariate polynomials, positivity tactic)

**Python:** sympy, numpy, cvxpy, clarabel

## License

MIT
