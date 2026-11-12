# Standalone finite hereditary observer: proposed next contract

Status: design only. No AST, frozen theorem, runtime integration, or completed hereditary observer is asserted here.

## Fixed inputs and exact scope

Retain the existing representative R and all source/minimum/final tuples unchanged. Use the separately calibrated rootObservation R only as a numeric root observation. Structural node size counts encoding nodes, including argument-list spines; it is not the old variable rank or the smaller source term size.

A runtime observer must take the original packed term and original pair(context code, Gamma code). Deletion successors use actual lookup/deleteAt and original arbitrary-cutoff erasePacked; their parameter is pair(the SAME context code, deleted Gamma). Lambda successors use pair(the SAME context code, domain :: Gamma), and their deletion enumeration starts at zero, including the newly bound variable.

## Finite bound and evaluation machine

Use potential length(Gamma) + 2 * nodeCount(raw packed term). Every deletion reduces the context length by one and preserves nodeCount. Every immediate raw child reduces nodeCount by at least one. A lambda child increases context length by one, so still decreases this potential. Nonbinding children retain context length. Positivity and strictness are actual internal graph facts; native calibration must be a separate theorem.

A possible uniform Program is a bounded explicit stack evaluator, not a self-referential Program definition: work frames carry packed value, context parameter, remaining depth, and a constructor phase; result frames carry encoded observations. Initialize with depth equal to this potential. Each child/deletion visit decreases depth. Loop count needs its OWN proved work bound: the potential bounds path length, NOT the number of nodes of the branching observation tree. A primitive-recursive upper bound may be obtained from the input context length, raw node count, and maximum lambda growth along a path; it must be proved before choosing the run bound. Reuse the existing bounded-machine proof pattern, not its unrelated termination theorem.

At a depth-zero frame return the root observation. At positive depth collect root metadata, all recursive child observations, and all in-range deletion observations. Encode these as a finite tagged tree. A depth bound alone does not yet implement a terminating machine with the right total work count.

## Matching and ordering

Application children and numbered extras are ordered; lambda has its single child in the extended context. Ordinary and numbered BASE arguments are typed MULTISETS, retaining multiplicity, not a fixed positional list. Sort numeric typed child observations before encoding BASE. Equivalent heads use the existing head-class encoding, not literal head identity. Deletion rows retain cutoff order because both compared roots have the same Gamma.

The existing semantic HereditaryView successor asks about EVERY pair of children sharing the old typed representative key, not only one chosen multiset matching. Merely sorting richer child observations proves a matching statement, not automatically that universal cross-pair clause. A separate uniformity theorem for recursive observations within an old typed-key class is needed to identify the numeric observer with that exact semantic relation. Do not silently replace its universal clause with positional or existential matching.

## Smallest useful next exact contract

Before a large evaluator, build a standalone one-layer deletion-row Program from an arbitrary supplied child observer Q : Program 2. It returns the ordered list of Q(erasePacked(type at k,k,input), pair(c,deleteAt(k,Gamma))) for every k < length(Gamma). Its native contract is exact list equality on typed packed inputs, with NO assumption on Q. Its internal contract exposes each indexed row from the actual run, actual range, actual lookup/delete/erase graphs and actual Q graph. Empty Gamma returns the literal empty list; no cutoff-zero special case is omitted under a lambda.

This is complementary to rootObservation Q, which already handles typed child traversal and sorted BASE. Together these provide a small, concrete one-step observation assembler without a new recursive machine. Only after exact one-step calibration, graph extraction, and semantic matching review should a depth-indexed machine AST be frozen.

## Nonclaims

Neither root calibration nor an arbitrary-Q deletion row gives final-C erasure cancellation, preservation by the current minimum, or internal correctness by native reflection. This design does not replace the old representative with a fingerprint, change the current tuple, or assert an all-depth observer has been implemented.
