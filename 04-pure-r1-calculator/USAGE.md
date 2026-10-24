# Calculator usage

Python 3.10 or later is sufficient. Runtime and packaging use only the standard
library. From this directory, run:

```sh
python3 -m r1calc endpoint 'w^w'
python3 -m r1calc add '2' 'w'
python3 -m r1calc resembles 'w' 'w+1' --json
python3 -m unittest discover -s tests -v
```

The first result is `w^(w) + w + 1`; the second is `w`. The `--json` option
produces a result object with schema `r1calc.result.v1`. A false Boolean result
is a completed calculation, not a command failure. The installed command is
`r1calc`; an offline installation with an existing pip is:

```sh
python3 -m pip install --no-deps --no-build-isolation .
r1calc endpoint 'w^2'
```

The included small PEP 517 backend builds wheels and source archives without
setuptools or dependency downloads. Python packaging is separate from the
paper and Lean build instructions in the README.

## Ordinal inputs and arithmetic

Use `w`, `omega`, or `ω` for omega. Accepted expressions contain natural
numbers, addition, parentheses, omega powers and right multiplication by a
natural. Powers associate to the right; parentheses enclose exponent sums:

```text
w^(w+1)*3 + w^2 + 7
(w+1)*2
w^w^2
```

These are **ordinal** operations: `1+w` normalizes to `w`, and `(w+1)*2`
normalizes to `w*2+1`. They are not commutative natural ordinal operations.
General multiplication, subtraction, arbitrary Python expressions and
epsilon-zero itself are outside the input grammar. `w*0` is the ordinal zero.
The text parser limits inputs to 65,536 characters, depth 64 and 1,000 digits
per natural literal; explicit limits are also available in the Python API.

Commands are `endpoint`, `principal-sum`, `norm`, `lean-term`, `add`, `mul-nat`,
`compare` and `resembles`. `compare` prints `<`, `=` or `>`; `resembles` tests
the arithmetic interval `a <= b <= endpoint(a)`.

```python
from r1calc import parse_ordinal, endpoint, pretty, add, nat, OMEGA

a = parse_ordinal("w^(w+1)*3")
print(pretty(endpoint(a)))
assert add(nat(2), OMEGA) == OMEGA
```

The original tuple API remains available: `CNF`, `ZERO`, `ONE`, `OMEGA`,
`nat`, `power`, `normal`, `add`, `mul_nat`, `principal_sum`, `endpoint`,
`resembles`, `unary_tree_size`, `pretty` and `lean_term`. Added helpers include
`last_exponent`, `compare` and `parse_ordinal`. Public arithmetic entry points
validate hereditary CNF, including every exponent. Invalid types, Boolean
coefficients, zero or negative block coefficients and nondecreasing exponents
raise `ValueError`. `normal` returns a Boolean syntax check.

CNF is a tuple of `(exponent_CNF, positive_coefficient)` blocks in strictly
decreasing exponent order; zero is `()`. `power(e,c)` constructs `omega^e*c`.
Coefficients remain compressed during arithmetic. `mul_nat(a,n)` means `a*n`.
`unary_tree_size` uses the expanded norm

```text
W(0) = 0
W(a) = sum c*(1+W(e)) over its CNF blocks (e,c).
```

It charges repeated exponent subtrees once per coefficient unit. It is not
binary input length, DAG size, execution time, pattern size or minimum
realization size. The endpoint's sharp triangular output-size bound concerns
this specific norm. The paper gives its mathematical proof, and `Norm.lean`
checks the general bound and matching tower witnesses at every natural size.
Large compressed coefficients may have enormous expanded norms without being
expanded by the implementation. Python memory, recursion and integer-printing
limits still apply; no general running-time bound is claimed.

## JSON interchange

Raw ordinal JSON is a nested array of `[exponent, coefficient]` blocks: zero
is `[]`, one is `[[[],1]]`, and omega is `[[[[[],1]],1]]`. A versioned wrapper
is also accepted:

```json
{"schema":"r1calc.ordinal.v1","cnf":[[[[[],1]],1]]}
```

`cnf_to_data` and `cnf_from_data` convert the raw arrays. Unlike the expression
parser, the JSON decoder requires CNF already in normal form and does not
silently sort or merge it. Supply a file as `@filename.json`, use `@-` for
standard input, or prefix inline JSON by `json:`:

```sh
python3 -m r1calc endpoint @ordinal.json --json
python3 -m r1calc endpoint 'json:[[[[[],1]],1]]'
```

CLI JSON inputs are bounded to 1 MiB. CNF decoding defaults to depth 64 and
10,000 block occurrences. Duplicate object keys, nonfinite numbers, malformed
blocks and unknown schema versions are rejected.

## Finite patterns and maps

`Pattern(n, relations, marked=None)` has vertices `0,...,n-1` in that fixed
linear order. `relations` is a nonempty tuple of frozensets of strict higher
edges. Validation checks strict upper triangles, nesting, transitivity and
respect for the preceding relation. The first preceding relation is the
fixed linear order. A marker, if present, is one integer vertex.

```python
from r1calc import Pattern, covers, embeds, morphisms

discrete = Pattern(2, (frozenset(),))
chain = Pattern(2, (frozenset({(0, 1)}),))
assert covers(discrete, chain)
assert not embeds(discrete, chain)
assert list(morphisms(discrete, chain)) == [(0, 1)]
```

Coverings are increasing injections preserving positive relation atoms.
Induced embeddings additionally reflect negative atoms. Markers are ignored
unless `preserve_marker=True`; that flag requires markers on **both** patterns.
A signature mismatch raises `ValueError`, rather than answering that no map
exists. `is_morphism` checks a supplied increasing image tuple.

Pattern JSON uses sorted edge arrays:

```json
{"schema":"r1calc.pattern.v1","n":2,"relations":[[[0,1]]],"marked":null}
```

The schema field may be omitted for the original raw interchange shape.
`pattern_to_data` and `pattern_from_data` handle conversion. Duplicate edges
and Boolean vertices/markers are invalid. CLI pattern files default to at
most 32 vertices and eight higher relations.

```sh
python3 -m r1calc validate-pattern pattern.json
python3 -m r1calc maps source.json target.json --induced --preserve-marker
python3 -m r1calc maps source.json target.json --all --limit 20
python3 -m r1calc patterns 4 --order 2 --limit 100
```

Map search examines increasing image tuples, at most `binomial(target.n,
source.n)` candidates. Pattern enumeration streams finite syntaxes and can
grow exponentially. The CLI defaults to 10,000 candidate checks and 20
output objects; `--max-candidates` and `--limit` change these bounds within
the documented CLI caps. Enumeration accepts `0 <= n <= 8`, order `1..8`,
output limit `1..1000`, and candidate limit `0..1000000`. The Python generators
have no implicit candidate cap unless `max_candidates` is supplied.

A completed negative map answer exhausts every candidate image. If a search
or output limit is reached, JSON has `complete:false` and exit code 3;
nonexistence is never inferred from a partial search. A completed existential
map answer can stop after its first witness; `enumeration_complete:false`
then records that further maps were not enumerated. Python raises
`SearchLimitError` when an explicit search budget expires. Invalid input exits
with code 2; completed calculations, including negative answers, exit with 0.

## Ambient traces and uses

```sh
python3 -m r1calc trace 'w' 'w+1' --marked 1
```

`pure_r1_trace` requires strictly increasing normal ordinal coordinates and
inherits their **ambient** arithmetic R1 relation. It does not recompute
recursive elementarity inside the resulting finite structure. The two-point
trace at omega and omega-plus-one has an inherited edge; this says nothing
about intrinsic finite Sigma1-elementarity. Higher-relation finite syntax is
supported, but there is no ordinal R2/R3 evaluator or realization/minimization
oracle.

Existing uses of this arithmetic and finite interface include small execution
certificate checks, checks of endpoint output sizes, and examples distinguishing
ambient traces from internally recomputed finite resemblance. It is also useful
for teaching examples, generating regression fixtures, and finding explicit
small finite covering or induced-map witnesses. These uses do not establish
global ordinal analysis or a general score of a reasoner's strength.

The tests compare compressed arithmetic with a separately implemented expanded
hereditary-word reference, and increasing-map search with an all-functions
finite reference. They include malformed input and explicit incomplete-search
cases. Finite tests are not proofs of the universal endpoint or semantic theorem.
The accompanying Lean modules prove their stated arithmetic and finite-checker
properties and prove Carlson's semantic endpoint characterization from the
constructed recursive Sigma1 relation. They do not verify execution of this
Python code. See the paper and
source guide for the exact theorem coverage and published inputs.
