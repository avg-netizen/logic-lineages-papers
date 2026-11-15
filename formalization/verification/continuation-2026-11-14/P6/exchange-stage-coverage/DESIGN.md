# Whole-frontier first-match coverage: exact1

Source: Mathlib/Computability/Primrec/List.lean nat_omega_rec association-list
filterMap stage, realized by ExchangeGraphStage.stage D G. Every frontier
occurrence computes dependencies and mapped answers against the SAME old table.
Therefore duplicate occurrences of a query compute the same G value. The first
successful matching occurrence wins; unrelated successful and skipped entries
preserve lookup in the remainder.

Target is a genuine object-language derivation from actual numeric frontier
membership, actual query D/mapGraph/G output against old, and actual stage graph.
No structurally manufactured output, semantic membership oracle, Boolean
reflection, generic F correctness premise, or standalone child extraction is
used. Some zero is covered; G output is explicitly successor value, not absence.

Proof plan: arithmetic strong induction on raw frontier code, internally
quantifying query/old/param/deps/answers/value/output. Empty raw has no members.
For a real cons, split node=query internally. Equal branch transports actual
query computation then applies checked first-head lookup. Distinct branch
recovers tail membership, eliminates actual head D/map/G output and actual tail
stage output, splits G zero/successor, applies the induction hypothesis and the
checked skip/distinct transport. Literal order/duplicates are unchanged.

Remaining: correctness of prior-table answers, original rank/frontier coverage,
coherence with independent child extraction, and typed validity. This theorem
pays arbitrary-frontier stage coverage conditional on actual query computation;
it does not claim those global recurrence obligations or original E completion.

Frozen for independent review/preflight; no proof authored/compiler launched.
