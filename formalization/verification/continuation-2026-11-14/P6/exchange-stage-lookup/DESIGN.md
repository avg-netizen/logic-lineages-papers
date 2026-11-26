# Actual stage first-match coherence (frozen exact3)

Source: Mathlib/Computability/Primrec/List.lean nat_omega_rec association-list stage;
Continuation20261114/ExchangeGraphStage.Definitions and its checked nativeStage.
Each frontier node uses the SAME old graph, D dependencies, actual mapGraph
omitting missing keys, and optional G result. Successful entries are emitted in
frontier order; skipped entries are omitted. Duplicate keys are retained and
lookup selects the FIRST emitted matching entry. A successful numeric value zero
is retained as Some zero (lookup output successor zero), distinct from absence.

The three internal targets remove constructed entry/table witness premises from
local stage lookup reasoning: successful head, omitted head, distinct successful
head. Tail-stage output in the last two targets is explicitly actual, not an
independently evaluated child or postulated table. All dependencies/recombination
facts remain actual graph premises. Pair, list and tail witnesses for head lookup
must be eliminated internally through program totality and functionality.

No new AST or source algorithm. No native reflection, dense memo replacement,
standalone-child/table equivalence, global frontier coverage, rank coherence,
typed extraction correctness, or recursive exchange completion is claimed.
This packet is a direct first-match induction prerequisite for those obligations.

Frozen, awaiting independent review/native preflight. No proof authored.
