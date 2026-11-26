# Independent final review: paper16 lem:operator (root, local continuation)

Accepted as the current numbered statement `lem:operator`
(decision.tex 179–202). Reviewer: root of the local three-party continuation,
not the lane A author. No reviewer native run.

## Comparator against the printed statement

The paper fixes ordinary inputs s,t and states that F is a monotone endomap of
the coherent natural families whose iteration from bottom reaches the least
fixed point in finitely many steps. `MarkedConstructorOperatorTargets.Operator`
quantifies every signature, every typed signature-valid ordinary s and t, and
uses the literal input inventory (types, names, ports, target, source heads).

- Endomap: for every retained family code M, the new family encodes
  successfully to `step M`, `step M` is again retained, and at every valid
  parameter the decoded field equals `MarkedConstructorValue.build`, the
  four-test marked value of the previously frozen and pre-scoped constructor
  comparator. `retained` is the existing filter of all raw family codes by the
  monotonicity and coherence tests, i.e. the paper's finite lattice of
  coherent monotone families. The `getD []` fallback in `step` is never the
  value on a retained input, because encoding success is a conclusion.
- Monotone: pointwise lattice order on all retained families.
- Stabilizes: every iterate from the join of the empty family list is
  retained; the iteration ascends; it is constant from the explicit bound
  (number of retained families) on; that value is a fixed point and is below
  every retained fixed point. The bound and iteration are executable.

No premise beyond typing and ordinariness of the two inputs is added.
`PrefixClosed`, a local hypothesis of the twelve supporting builder contracts,
is discharged inside `exact_Operator` from the literal inventory. The
companion `exact_SourceLookup` shows at that inventory that every lookup the
Select, Copy/Stat and FAbs tests request succeeds in the carrier, including
the canonical opening slot and context, so no valid source rule is discarded
by a failing branch.

## Evidence

Final core union receipt 1795032756929340478-76. Recursive compiler-free
evidence reproduced independently and JSON-identical to the author's
A/OPERATOR-FINAL-EVIDENCE.json: 197 source-matched modules, 37 frozen hashes,
14 exact aliases (exact_Operator, exact_SourceLookup and the twelve builder
aliases), each depending only on propext, Classical.choice and Quot.sound.
No unsafe, opaque, implemented_by, extern, partial, axiom, sorry or
native_decide in the MarkedConstructor module family. Failed drafts are
preserved under paper16/failed/.

## Limits

This is the operator lemma only. That the fixed point's bits coincide with
derivability (thm:adequacy), the structural interpretation
(lem:structural-interpretation), the decision theorem and height results
remain pending. No full-root or CI claim.
