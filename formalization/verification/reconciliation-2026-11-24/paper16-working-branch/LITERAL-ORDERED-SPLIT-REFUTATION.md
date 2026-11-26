# Paper 16: the literal ordered split is false, even for deletion

The installed `dCore` checker is now numerically calibrated on **all** raw
inputs against the original `NumberedWindowDirectAlgorithm.direct`. The
theorem keeps the exact scalar, positive-relation and permutation-observer
calibrations explicit; it is not limited to well-formed inputs. The proof
checks witness arity and tags, every inserted row and its dominator check,
the projected inserted targets, both partitions, and the scalar guards.
Malformed witnesses are rejected rather than assumed away.

For a concrete specialization, take the scalar checker to be constantly one,
and positive edges to be constantly zero. All direct edges then delete at
least one occurrence; their strict decrease in decoded length proves
well-foundedness. With the fixed original `functionalUnion`, concatenate
[0,0] and [1] to obtain [0,0,1]. The same installed direct checker accepts
[1,0] using kept [1,0], removed [0] and no insertions. Any independently
unchanged or decreased first part consists only of zeros; the second part
contains only ones. Their literal ordered concatenation cannot be [1,0].

This is also a refutation of the exact internal
`ConditionalJUnionTargets.MultisetSplit` at that specialization, for
every context index, not just a list computation. The original ordered
union and direct edge are true hypotheses in the standard least model.
Arithmetic truth of the graph and soundness of the actual internal calculus
would turn a purported proof of the split into impossible numeric witnesses.
The same specialization satisfies `CarrierUnion` and `UnionClosure`.
The certified split **up to permutation** and the checked J closure
therefore remain the usable route. This does not refute the certified
permutation split, the closure itself, or a theorem restricted to a
different checker or a different choice of representative.

No paper source or numbered acceptance is changed. The adjacent evidence
records the named axioms, source digests, and exact local receipts. Hosted
whole-repository CI is separate.
