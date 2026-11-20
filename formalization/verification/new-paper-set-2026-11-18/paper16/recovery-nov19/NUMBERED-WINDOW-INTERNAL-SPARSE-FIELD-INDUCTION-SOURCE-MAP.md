# Source map: three-case internal induction for actual sparse raw field codes

Paper 16 presents finite typed contexts as one arithmetic carrier
(`ordinals.tex` 12–29); 70–76 specifies finite numerical class/path witnesses,
and 84–98 and 112–127 use their arithmetic interpretation and path transport.
The repository field coder `NumberedWindowFieldAlgorithm.pack` uses nil 0
and the actual sparse polynomial successor `pair head rawTail + 1` as cons.
It is not Mathlib `Nat.pair`. The actual `fieldCons` AST and strict raw-tail
descent were independently checked in supporting packet 616.

The new comparator uses the original arithmetic compiler at the literal
`fieldCons` with inputs [head, tail] and output raw code. A code has an
outer cons only through two genuine first-order existential constructor
coordinates. A nonzero code can have no cons preimage; this is an explicit
malformed-first-cell case, not the assertion that every positive value is
a cons. A cons with recursively malformed tail is also covered:
the invariant is invoked on its actual strictly smaller *raw* tail with
no assumption that the tail decodes. The arithmetic input domain remains
all naturals and no equation of the existing parser or checker is altered.

`SparseFieldInductionSchema` asks for a genuine proof tree in the unchanged
finitary ID1 calculus, for any invariant from its existing first-order
language with one positive inductive definition (not an added inductive
predicate, semantic schema, or external theorem-as-rule). It assumes only
the three explicit original-language branches: invariant at 0, invariant
for nonzero code without a cons preimage, and constructor preservation
from the invariant at the actual tail. Its conclusion is the universal
object theorem. `SparseFieldInductionAtCode` asks for contextual use at an
arbitrary object-language term with the same three derivation premises.

Proof route: use the retained course-of-values proof derived from ordinary
object arithmetic induction, split first by object equality with zero and
then the object formula for cons existence, eliminate the two witnesses
in the positive case, and apply the checked strict order of the cons
tail. The old two-case max-square list induction is not the induction
rule for these sparse codes; only its generic binding conventions
are useful. No decoder, path transducer, arithmetic matching, or numbered
accessibility proof is asserted here.
