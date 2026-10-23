# Pure R1 calculator

A standalone calculator for Carlson's pure first-order resemblance below
epsilon zero, with a finite-pattern library, an explanatory paper and checked
Lean proofs.

- [Paper PDF](paper.pdf) · [TeX source](paper.tex)
- [Python commands and formats](USAGE.md)
- [Lean proof coverage](FORMALIZATION.md) · [Lean project](lean/)
- [Sources and mathematical dependencies](SOURCES.md)
- [Verification record](VERIFICATION.md)

For an ordinal `a`, the endpoint `H(a)` is the largest `b` with `a <=_1 b`
in the standalone pure R1 structure. The implementation uses hereditary
Cantor normal forms with compressed positive natural coefficients. For
example, `H(omega)=omega+1` and
`H(omega^omega)=omega^omega+omega+1`. The finite-pattern interface handles
validity, coverings, induced embeddings and optional markers.

Python uses only the standard library. From this directory:

```python
from r1calc import OMEGA, ONE, add, endpoint, resembles

assert endpoint(OMEGA) == add(OMEGA, ONE)
assert resembles(OMEGA, add(OMEGA, ONE))
```

```sh
python3 -m unittest discover -s tests -v
```

For the full recorded check, after setting up the documented dependencies, use
`python3 scripts/verify.py --lean --paper`.

The [usage guide](USAGE.md) gives the readable ordinal grammar, command-line
examples, JSON format and finite-enumeration limits. No installation or private
repository is needed to run from source.

For Lean, install the toolchain pinned in `lean/lean-toolchain`. From `lean/`,
acquire the pinned public dependencies and their compiled Mathlib cache:

```sh
lake update
lake exe cache get
```

Then return to this directory and compile the project in dependency order:

```sh
python3 scripts/check_lean.py R1Calculator/Ordinal.lean R1Calculator/Patterns.lean R1Calculator/Examples.lean R1Calculator.lean
```

The helper serializes compilers and sets explicit heap, virtual-address,
CPU and wall-time limits. It reads only installed dependencies and writes this
project's ignored build directory. An existing public Mathlib cache can be used
locally; the committed Lake configuration contains no machine-specific paths.

The Lean development proves normal-form preservation, the endpoint's actual
ordinal-denotation recursion, interval-check correctness, and finite-pattern
checker and map laws. Carlson's theorem identifying that arithmetic interval
with recursive Sigma-one elementarity is a cited mathematical input, not a new
Lean axiom or a theorem re-proved here. Python is separately tested; the package
does not claim a formal refinement proof from Python to Lean. The paper's sharp
expanded-tree size bound is an ordinary mathematical proof.

The ordinal evaluator is for pure R1 below epsilon zero. The order-two pattern
objects are finite syntax, with no order-two ordinal assignment. Neither pattern
counts nor finite tests compute Carlson's transfinite order types.

Build the paper with `python3 build_pdf.py`. The default uses cached Tectonic
resources and Computer Modern, following the repository's other papers.
