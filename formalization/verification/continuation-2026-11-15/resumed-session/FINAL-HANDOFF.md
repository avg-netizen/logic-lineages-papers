# Completed continuation — 16 November 2026

Four exact supporting contracts are accepted on
`formalization/cumulative-continuation-2026-11-15`, continuing from
`1144d37f04508af0b09ea3f6bb8b3007307f4228`. The supporting-contract total rises
from **729 to 733**. The original numbered register remains **175 checked,
2 inherited, 12 pending /189**.

## Accepted mathematics

| Packet | Exact declarations | Native closure | Audited candidate theorems |
| --- | --- | ---: | ---: |
| Paper 6: `OriginalEnumerationEquation` | `exactPreviousAnswers`, `exactEnumerationEquation` | 3,881 | 42 |
| Paper 12: `PrescribedRuntimeCallCongruence` | `exactPrescribedTraces`, `exactTupleAndCall` | 2,212 | 44 |

The Paper 6 packet proves that the previous own-root table, observed at the
actual rank `R(node)` (fuel), returns exactly the ordered standalone child
answers. Coverage, rank-zero emptiness, definedness, and extraction are proved
internally. The second contract identifies the literal original enumeration
recurrence with `G`: enumeration returns the payload, while `G` returns
`Some(payload)`. In particular, `Some(0)` for the empty-list code stays distinct
from `None`. Ordered prior/opened children and duplicates are retained, without
new public recursive-value or lookup-agreement assumptions. All fourteen
original candidate source files remain byte-identical to the inherited draft.

The Paper 12 packet proves the literal tuple and call syntax values and the
exact numerical certificate recipes. Input certificate numbers remain arbitrary
natural numbers, including malformed encodings. The proof retains dynamic closed
coordinates, the duplicated sum certificate in pair multiplication, tail-first
tuple recursion, and the original tag/arity/header construction order. Its
runtime contract consumes actual argument-validity and input equality
certificates and produces tuple/call acceptance at the same installation,
context, index, and fuel. Zero-arity and header reflexivities are derived
internally. Seven new proof and assembly modules complete this packet.

Acceptance records:

- [Paper 6 acceptance](../resumed-paper06/ACCEPTED.json).
- [Paper 12 acceptance](../resumed-paper12/ACCEPTED.json).
- [Paper 6 independent review](../resumed-independent-review/P6-FINAL-REVIEW.json).
- [Paper 12 independent review](../resumed-independent-review/P12-FINAL-REVIEW.json).

## Native verification and preservation

The two focused closures contain **6,008 distinct source-matched local
modules**, with 85 shared modules. Every final receipt row succeeds and matches
the live source. Both preflights and all four exact aliases pass. All 86 candidate
theorem audits use only the permitted foundational axioms: `propext`,
`Classical.choice`, and `Quot.sound`.

The unchanged native profile is one thread, a 2,048 MiB Lean heap cap,
1,536 MiB resident-memory cap, 2,048 MiB minimum free memory, 90 CPU seconds,
and 180 wall seconds per module. Maximum observed RSS in the final closures is
1,532.840 MiB for Paper 6 and 1,197.934 MiB for Paper 12. The checker, audit
implementation, toolchain, and dependency pins match the starting commit.
The setup wrapper raises only Python's import-traversal recursion limit to
20,000; it does not raise any Lean verification limit.

Three inherited syntax proofs required removal of compiler-reported unused
`simp` arguments. A fourth memory failure was resolved by splitting nine
constructor-branch proofs between two modules while preserving their complete
declarations and proof bodies. Their native audits cover four and five
theorems, respectively. The existing constructor-layer exact gate also passes.

Paper 12 repairs make numeral aliases, vector constructors, and the empty bound
environment explicit. The final tuple-successor `simpa` has a narrowly scoped
elaboration transparency option so implicit dependent indices can unfold their
ordinary definitions. Pinned Lean source and Mathlib's `Vector.tail_map`
substantiate this use. Kernel checking, theorem assumptions, axiom auditing,
and resource limits are unchanged.

All four memory-stop sources and all seven failed or diagnostic Paper 12
attempts are preserved with raw logs, receipt rows, full compressed receipts,
and hash manifests. Independent review verified all 133 source hashes across
the seven Paper 12 snapshots. Complete successful evidence is available in
[Paper 6 native evidence](../resumed-paper06/native/FINAL-NATIVE-MANIFEST.json),
[Paper 12 native evidence](../resumed-paper12/native/FINAL-NATIVE-MANIFEST.json),
and the [combined native reconciliation](FINAL-NATIVE-UNION.json).

Verification covers these focused dependency closures. No full-root or remote
CI result is claimed. All compiler jobs for this checkpoint have completed.

## Remaining mathematical work

Paper 6 still needs the original enumeration field/depth coverage and final
`Q` integration, followed by full internal `I/C` and accessibility. Paper 12
still needs full composition producer assembly, primitive-recursion certificate
accumulator correctness, and the original source12 `HB3` discharge. These remain
separate obligations; this checkpoint does not adopt additional numbered paper
statements.

The [reviewed successor plan](../resumed-independent-review/NEXT-STEPS.md)
identifies the next bounded proof packets and their exact source boundaries.
