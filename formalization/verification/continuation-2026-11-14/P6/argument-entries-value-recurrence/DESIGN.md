# Actual cached-value recurrence: exact2

This is value recombination against the SAME previous association table, not
presence/order alone. Actual frontier member, actual D output and actual
mapGraph answers, actual stage output and Some(value) first-match lookup imply
the original concrete optional layer returns Some(value) on those answers.

Proof plan: internally bind the actual inner step output, use the paid original
outer-Some construction, then whole-stage coverage. Functionality of lookup
identifies its successor output with Some(value); output transport yields the
actual original layer equation. No public layer output premise is added.
Duplicates are covered by the same-key computation's functionality.

Second contract applies this to actual original graph successor with the
actual previous graph, same seed and parameter, and actual rank-subtraction
frontier. Explicit subtract input order [index,seed] means seed-index.

Zero cached value (inner None) remains Some0 at lookup; no missing=zero cast.
This establishes local same-table recurrence, NOT equality of cached values
with independently rooted child extraction. That global coherence and typed
Some-definedness remain open. No native reflection or algorithm substitution.
Frozen for review/preflight; no proof authored.
