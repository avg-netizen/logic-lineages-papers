# Original indexed replacement and multiset certificate tests

The two frozen targets state primitive recursiveness of the unchanged
`NumberedMultisetCertificate.replacementTest` and `multisetTest`. They quantify
over each explicit fixed finite signature, arity and context, with all ordered
lists and the complete original certificate varying as inputs. This supplies
the actual Mul rule used by paper06's finite auxiliary reduction and arithmetic
relation discussion at lines 537–556.

The implementation proof consumes the witness list while retaining the remaining
inserted list and a Boolean success accumulator. Its exact calibration returns
the original recursive test for every list, including missing or extra
witnesses, out-of-range removed indices and repeated indices. The final state
must have no unconsumed inserted occurrences. Each successful witness uses the
original `markTarget`, including marking beneath initial lambdas. It does not
replace marking by the root-only Put operation.

The multiset proof composes the original kept/removed/inserted lists, exact list
permutation tests, nonempty removal and indexed replacement. It retains
multiplicity and allows empty insertion when the original checker allows it.
No well-formedness, mark-correctness or effectivity premise is added. These are
supporting computational results; whole-source simulation, arithmetic formulas
and internal ID1 accessibility remain distinct obligations.
