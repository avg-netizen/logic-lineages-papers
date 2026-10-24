# Pure R1 calculator

[![Pure R1 Lean verification](https://github.com/avg-netizen/logic-lineages-papers/actions/workflows/pure-r1-lean.yml/badge.svg?branch=main)](https://github.com/avg-netizen/logic-lineages-papers/actions/workflows/pure-r1-lean.yml)

A standalone calculator for Carlson's pure first-order resemblance below
epsilon zero, with a finite-pattern library, an explanatory paper and checked
Lean proofs.

- [Paper PDF](paper.pdf) · [TeX source](paper.tex)
- [Python commands and formats](USAGE.md)
- [Lean proof coverage](FORMALIZATION.md) · [Lean project](lean/)
- [Sources and mathematical dependencies](SOURCES.md)
- [Verification record](VERIFICATION.md)
- [Public CI compilation and artifacts](CI.md)

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

The [usage guide](USAGE.md) gives the readable ordinal grammar, command-line
examples, JSON format and finite-enumeration limits. No installation or private
repository is needed to run from source.

For Lean, install the toolchain pinned in `lean/lean-toolchain`. From `lean/`,
acquire the pinned public dependencies and their compiled Mathlib cache:

```sh
lake update
lake exe cache get
```

Then return to this directory and run the complete verification, which compiles
all local modules in dependency order:

```sh
python3 scripts/verify.py --lean --paper
```

The helper serializes compilers and sets explicit heap, virtual-address,
CPU and wall-time limits. It reads only installed dependencies and writes this
project's ignored build directory. An existing public Mathlib cache can be used
locally; the committed Lake configuration contains no machine-specific paths.

The Lean development proves that the computed endpoint is the greatest actual
ordinal reachable by Carlson's recursively defined pure R1 relation. It includes
the semantic recursion, finite induced-copy criterion, constructive copies and
obstructions, and the arithmetic bridge. There is no external Carlson
correctness assumption. The paper's sharp expanded-tree output-size theorem,
including a witness at every size, is formalized too. [Selected constructions](REUSE.md)
were adapted from the 3.1.3 Lean development without adding a dependency on it.

The formalization uses standard Lean/Mathlib foundations. Python execution is
separately tested; there is no formal Python-to-Lean refinement proof.

The ordinal evaluator is for pure R1 below epsilon zero. The order-two pattern
objects are finite syntax, with no order-two ordinal assignment. Neither pattern
counts nor finite tests compute Carlson's transfinite order types.

Build the paper with `python3 build_pdf.py`. The default uses cached Tectonic
resources and Computer Modern, following the repository's other papers.
