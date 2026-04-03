# Sostactic

This is a collection of Lean4 tactics for proving polynomial inequalities via _sum-of-squares (SOS) decompositions_, powered by a Python backend. You can use it via Python or Lean.

These tactics are significantly more powerful than `nlinarith` and `positivity` -- i.e., they can prove inequalities they cannot. In theory, they can be used to prove any of the following types of statements
- prove that a polynomial is nonnegative globally
- prove that a polynomial is nonnegative over a semialgebraic set (i.e., defined by a set of polynomial inequalities)
- prove that a semialgebraic set is empty, i.e., that a system of polynomial inequalities is infeasible

To see more about how it works, read the [blog post](https://mmaaz.ca/writings/sostactic.html). Full documentation is provided towards the end of this `README`; feel free to point your coding agent at it.

## Quick Examples

```lean
import Sostactic

-- AM-GM inequality
example (x y : ℝ) : 2 * x * y ≤ x^2 + y^2 := by
  sos_decomp

-- Motzkin polynomial: ratio of SOS
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (degree := 2)

-- 4x³ - 3x + 1 ≥ 0 on [0, 1] (touches 0 at x = 1/2)
-- linarith, positivity, and nlinarith all fail
example (x : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ 1 - x) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (order := 2)

-- two disjoint disks centered at (0,0) and (3,3)
-- linarith and nlinarith fail
example : ¬∃ x y : ℝ, 0 ≤ 1 - x^2 - y^2 ∧ 0 ≤ 1 - (x - 3)^2 - (y - 3)^2 := by
  rintro ⟨x, y, h1, h2⟩
  schmudgen_empty (order := 1)
```

Look at `Sostactic/Examples.lean` for more interesting examples!

## Setup

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean 4 toolchain manager)
- Python 3.10+

### 1. Add the dependency

If your project uses `lakefile.toml`:

```toml
[[require]]
name = "sostactic"
git = "https://github.com/mmaaz-git/sostactic.git"
rev = "main"
```

Or if your project uses `lakefile.lean`:

```lean
require sostactic from git
  "https://github.com/mmaaz-git/sostactic.git" @ "main"
```

Then fetch and build:

```bash
lake update sostactic
lake build
```

> **Note:** Sostactic tracks Mathlib `v4.29.0-rc8`. If your project uses a different Mathlib version, you may need to align them. When creating a new project, the default Mathlib version should match.

### 2. Set up the Python environment

Create a virtual environment in your project root and install the dependencies:

```bash
python3 -m venv .venv
.venv/bin/python3 -m ensurepip
.venv/bin/python3 -m pip install -r .lake/packages/Sostactic/python/requirements.txt
```

That's it. Sostactic auto-discovers `.venv/bin/python3` in your project root.

> **Tip:** Add `.venv/` to your `.gitignore`.

### Advanced: custom Python path

If your Python lives elsewhere, set the `SOSTACTIC_PYTHON` environment variable:

```bash
export SOSTACTIC_PYTHON=/path/to/your/python3
```

## How it works

This package has 3 possible ways to use it: as a Python API, as a Python CLI, and as a Lean package. The Lean tactics call the Python CLI to generate the certificate, and then the certificate is checked inside Lean. The Python program uses `cvxpy`, a convex optimization solver, due to the well-established correspondence between SOS polynomials and semidefinite programming (SDP). One issue is that the SDP solution is numerical: we use a rationalization and projecting step, with some additional numerical tricks, to get an _exact_ answer, which is then checked in Lean.

A caveat is that, due to numerical issues, exactification may fail, for a variety of reasons. In the spirit of interactive theorem provers, the solver provides suggestions about how to fix the solution by passing additional arguments.

For more details on the theory and algorithms, see the [blog post](https://mmaaz.ca/writings/sostactic.html).

The rest of this `README` introduces the Python API, the Python CLI, and then the Lean tactics.

## Python API

The entire Python program is contained in `python/sos.py`, with tests in `python/test_sos.py`. There are 5 main functions:

### `sos_decomp(p, denom_degree_bound=0, denom_template=None)`

Prove that a polynomial `p` is globally nonnegative by finding an exact SOS certificate.

```python
from sympy import symbols, Poly
from python.sos import sos_decomp

x, y = symbols('x y')
result = sos_decomp(Poly(x**2 + y**2, x, y))
print(result["success"])  # True
print(result["exact_sos"])  # weighted SOS terms: [(weight, poly), ...]
```

With `denom_degree_bound=0` (default), finds a pure SOS decomposition: `p = w₁s₁² + w₂s₂² + ...`

With `denom_degree_bound > 0`, finds SOS polynomials `d` and `n` such that `d·p = n`, handling polynomials like Motzkin's that are nonneg but not themselves SOS:

```python
x, y, z = symbols('x y z')
motzkin = Poly(x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2, x, y, z)
result = sos_decomp(motzkin, denom_degree_bound=2)
print(result["exact_num_sos"])  # numerator SOS decomposition
print(result["exact_den_sos"])  # denominator SOS decomposition
```

You can also pass an explicit `denom_template` as a sympy expression with free parameters (e.g., `a*x**2 + b*y**2 + c*z**2`).

On failure, `result["diagnostics"]` contains rank info and `result["suggestion"]` has a hint for what to try next.

### `putinar(target, constraints, order, basis_overrides=None)`

Prove that `target >= 0` on the semialgebraic set `{x : g₁(x) >= 0, ..., gₘ(x) >= 0}` using Putinar's Positivstellensatz.

```python
from python.sos import putinar

x = symbols('x')
result = putinar(
    target=4*x**3 - 3*x + 1,
    constraints=[x, 1 - x],
    order=2
)
print(result["success"])  # True
print(result["exact_certificate_blocks"])  # certificate blocks with multipliers and SOS
```

The `order` is the global relaxation order `r`. Each block with multiplier `h` is truncated by
`deg(h * sigma) <= 2r`, so `sigma` uses monomials of degree at most `floor((2r - deg(h)) / 2)`.

### `schmudgen(target, constraints, order, basis_overrides=None)`

Same interface as `putinar`, but uses Schmüdgen's Positivstellensatz, which uses products of all subsets of constraints as multipliers. More powerful than Putinar (works on any compact set), but the SDP grows exponentially in the number of constraints.

```python
from python.sos import schmudgen

x = symbols('x')
result = schmudgen(
    target=x*(1 - x),
    constraints=[x, 1 - x],
    order=1
)
```

### `putinar_empty(constraints, order, basis_overrides=None)`

Prove that `{x : g₁(x) >= 0, ..., gₘ(x) >= 0}` is empty. Equivalent to `putinar(-1, constraints, order=order)`.

```python
from python.sos import putinar_empty

x = symbols('x')
result = putinar_empty(constraints=[x, -x - 1], order=1)
print(result["success"])  # True — the set {x >= 0, x <= -1} is empty
```

### `schmudgen_empty(constraints, order, basis_overrides=None)`

Same as `putinar_empty`, using Schmüdgen's Positivstellensatz.

### Return value

All functions return a dict with at least:
- `"success"`: whether an exact certificate was found
- `"suggestion"`: on failure, a hint for what to try (e.g., increase degree, use a template)

On success, the result also contains the exact certificate data (SOS terms, Gram matrices, certificate blocks). On failure, `"diagnostics"` or `"block_diagnostics"` contain per-block exactification diagnostics useful for tuning `basis_overrides`. The backend also returns a heuristic `basis_override_suggestion` and a top-level `"suggestion"` string you can paste into the CLI or Lean tactic. Suggestions are derived from the failed numeric solution itself; they do not trigger additional hidden SDP solves.

## Python CLI

The CLI provides the same 3 commands (`sos_decomp`, `putinar`, `schmudgen`) and outputs JSON certificates.

### `sos_decomp`

```bash
python python/sos.py sos_decomp --poly "x**2 + y**2" --vars "x y"

# with denominator search
python python/sos.py sos_decomp --poly "x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2" \
    --vars "x y z" --denom-degree-bound 2

# with explicit denominator template
python python/sos.py sos_decomp --poly "x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2" \
    --vars "x y z" --denom-degree-bound 2 --denom-template "a*x**2 + b*y**2 + c*z**2"

# save certificate to file
python python/sos.py sos_decomp --poly "x**2 + y**2" --vars "x y" --out cert.json
```

### `putinar`

```bash
# prove 4x^3 - 3x + 1 >= 0 on [0, 1]
python python/sos.py putinar --poly "4*x**3 - 3*x + 1" --constraints "x, 1-x" \
    --vars "x" --order 2

# prove emptiness (--poly defaults to -1)
python python/sos.py putinar --constraints "x, -x-1" --vars "x" --order 1
```

### `schmudgen`

```bash
# prove x(1-x) >= 0 on [0, 1]
python python/sos.py schmudgen --poly "x*(1-x)" --constraints "x, 1-x" \
    --vars "x" --order 1

# prove emptiness
python python/sos.py schmudgen --constraints "1-x**2-y**2, x**2+y**2-2" \
    --vars "x y" --order 1
```

### CLI arguments

| Argument | Description |
|----------|-------------|
| `--poly` | Target polynomial (default `"-1"` for `putinar`/`schmudgen`) |
| `--constraints` | Comma-separated list of constraint polynomials |
| `--vars` | Space-separated list of variable names |
| `--denom-degree-bound` | Denominator degree bound (for `sos_decomp`) |
| `--denom-template` | Explicit denominator template (for `sos_decomp`) |
| `--order` | Global relaxation order for `putinar`/`schmudgen` |
| `--basis-overrides` | Per-block SOS degree caps, e.g. `"0:2,3:0"` |
| `--out` | Path to write JSON certificate |

### Output format

The CLI outputs a JSON certificate. For a successful `sos_decomp`:

```json
{
  "success": true,
  "kind": "sos",
  "status": "optimal",
  "exact_sos": [
    {"weight": "1", "poly": {"expr": "y", "gens": ["x", "y"]}},
    {"weight": "1", "poly": {"expr": "x", "gens": ["x", "y"]}}
  ],
  "exact_identity": {"expr": "0", "gens": ["x", "y"]},
  "exact_residual": {"expr": "0", "gens": ["x", "y"]},
  ...
}
```

This says `x² + y² = 1·y² + 1·x²`. For Positivstellensatz certificates, the result includes `exact_certificate_blocks` with multiplier/SOS pairs for each constraint block.

On failure, the output includes diagnostics and a suggestion:

```json
{
  "success": false,
  "status": "infeasible",
  "suggestion": "not SOS — try adding a denominator with denom_degree_bound=2"
}
```

## Lean tactics

### `sos_decomp` — Global nonnegativity

Proves that a polynomial `f` is nonnegative globally by finding an SOS decomposition, optionally with a denominator to decompose it into a ratio of SOS polynomials. By Artin's theorem, any globally nonnegative polynomial can be decomposed into a ratio of SOS.

Goals can be in any of these forms: `0 ≤ f`, `f ≥ 0`, `a ≤ b`, or `a ≥ b`.

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

Proves `0 ≤ f` given polynomial inequality hypotheses, using Putinar's or Schmüdgen's Positivstellensatz. Hypotheses can be in any of these forms: `0 ≤ g`, `g ≥ 0`, `a ≤ b`, or `a ≥ b`.

```lean
-- Putinar: requires Archimedean (compact) constraints
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (order := 2)

-- Schmüdgen: requires compact constraints, uses products of gᵢ
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) :
    0 ≤ x * (1 - x) := by
  schmudgen_decomp (order := 1)
```

### `putinar_empty` / `schmudgen_empty` — Emptiness of semialgebraic sets

Proves `False` from contradictory polynomial inequality hypotheses, showing the feasible set is empty.

```lean
-- {x ≥ 0, x ≤ -1} is empty
example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ -1) : False := by
  putinar_empty (order := 1)

-- disjoint disks
example (x y : ℝ) (h1 : x^2 + y^2 ≤ 1) (h2 : x^2 + y^2 ≥ 2) : False := by
  schmudgen_empty (order := 1)
```

### Common parameters

| Parameter | Description |
|-----------|-------------|
| `order := n` | Relaxation order for `putinar_decomp` / `schmudgen_decomp` / emptiness tactics |
| `degree := n` | Degree bound for `sos_decomp` |
| `denom_template := "..."` | Explicit denominator template (for `sos_decomp`) |
| `basis_overrides := "0:2,3:0"` | Per-block SOS degree caps used to shrink exactification search space |
| `cert := "path.json"` | Load a pre-generated certificate from file |

### Certificate Import

The SDP solver can be slow for large problems. You can pre-generate certificates and load them from JSON files, so the solver doesn't re-run on every file reload:

```lean
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (cert := "certs/motzkin.json")
```

Lean still independently verifies the certificate — the JSON file is untrusted.

### Interactive goals

If one of the sub-goals does not close automatically, the tactic leaves it as a **named goal** for you to close interactively. For `sos_decomp` and the Positivstellensatz decomp tactics, the goals are:

- `sos_identity` / `pstv_identity` — the polynomial identity (normally closed by `ring_nf`)
- `sos_nonneg` / `pstv_nonneg` — the nonnegativity claim (normally closed by `positivity`)

For `sos_decomp` with a denominator, the goals are `hD_ne`, `hmul`, `hD_nonneg`, and `hN_nonneg`.

You can close them with `case`:

```lean
example (x y : ℝ) : 0 ≤ x^2 + y^2 := by
  sos_decomp
  case sos_identity => ring
  case sos_nonneg => positivity
```

## Advanced Usage

### Pre-generating certificates for large problems

The SDP solver can be slow for large polynomials. You can use the Python CLI to generate a certificate once (e.g., overnight), save it to a JSON file, and then load it in Lean so the solver doesn't re-run on every file reload:

```bash
# generate the certificate
python python/sos.py sos_decomp \
    --poly "x**4*y**2 + x**2*y**4 + z**6 - 3*x**2*y**2*z**2" \
    --vars "x y z" --denom-degree-bound 2 --out certs/motzkin.json

# or for Positivstellensatz certificates
python python/sos.py putinar --poly "4*x**3 - 3*x + 1" \
    --constraints "x, 1-x" --vars "x" --order 2 --out certs/chebyshev.json
```

Then in Lean:

```lean
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (cert := "certs/motzkin.json")

example (x : ℝ) (h1 : 0 ≤ x) (h2 : x ≤ 1) :
    0 ≤ 4 * x^3 - 3 * x + 1 := by
  putinar_decomp (cert := "certs/chebyshev.json")
```

Lean still independently verifies the certificate — the JSON file is untrusted.

### Troubleshooting exactification failures

The SDP solver finds a numerical solution, which then needs to be converted to exact rationals. This "exactification" step can fail for several reasons. When it does, the solver returns diagnostics and suggestions.

**Increase the relaxation order.** If the solver returns infeasible, the truncation may be too small. Try increasing the order:

```lean
-- order 1 might not be enough
example ... := by putinar_decomp (order := 2)
-- try order 3
example ... := by putinar_decomp (order := 3)
```

**Use a denominator.** For `sos_decomp`, if the polynomial is nonneg but not SOS (like Motzkin's), you need a denominator:

```lean
-- fails without denominator
-- example ... := by sos_decomp
-- works with denominator degree 2
example ... := by sos_decomp (degree := 2)
```

**Use basis overrides.** When exactification fails after the SDP is already feasible, the solver suggests `basis_overrides` to shrink selected SOS blocks. Run once without them, then rerun explicitly with the suggested override:

```lean
example ... := by putinar_decomp (order := 3) (basis_overrides := "1:2,2:3")
```

The format is `"block:degree,block:degree,..."` where each pair restricts a specific block to a smaller SOS degree cap. For example, `0:2` means block 0 may only use monomials of degree at most 1.

**Use a denominator template.** For `sos_decomp` with a denominator, you can guide the solver by specifying the form of the denominator with free parameters:

```lean
example (x y z : ℝ) :
    0 ≤ x^4 * y^2 + x^2 * y^4 + z^6 - 3 * x^2 * y^2 * z^2 := by
  sos_decomp (degree := 2) (denom_template := "a*x^2 + b*y^2 + c*z^2")
```

**Try Schmüdgen instead of Putinar.** For constrained problems, Schmüdgen's theorem is more powerful (it uses products of all subsets of constraints). If Putinar fails, Schmüdgen may succeed:

```lean
-- putinar might fail here
-- example ... := by putinar_decomp (order := 2)
-- schmudgen uses product multipliers
example ... := by schmudgen_decomp (order := 2)
```

**Pre-generate the certificate.** If the solver is too slow to run interactively, generate the certificate with the Python CLI and load it in Lean (see [Pre-generating certificates](#pre-generating-certificates-for-large-problems) above).

### Heartbeat and timeout issues in Lean

For large polynomials, Lean's proof reconstruction can hit the default heartbeat limit. You can increase it locally:

```lean
set_option maxHeartbeats 800000 in
example ... := by sos_decomp (degree := 2)
```

If one of the sub-goals does not close automatically, it will be left as a named goal (e.g., `sos_identity` or `sos_nonneg`) for you to close manually. See [Interactive goals](#interactive-goals).

## Dependencies

**Lean:** [Mathlib](https://github.com/leanprover-community/mathlib4) (multivariate polynomials, positivity tactic)

**Python:** sympy, numpy, cvxpy, clarabel

## License

MIT
