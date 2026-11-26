# Actual nil base and tail-only local coherence: exact2

The original argumentEntries layer ignores the head's cached value; it reads
answer slot 1 (tail). Original cons dependencies are [head,tail], mapGraph omits
missing lookups, so BOTH head lookups must still be present. Their cached
values may differ. The tail lookups must have the SAME cached value explicitly.
This equality is not inferred from domain/order, nor from native calibration.

Nil: actual constructor gives D empty and layer Some(Some[]) = 2, any old
table. Actual stage coverage yields precisely the cached lookup 2.

Cons: internally bind actual dependency output, both mapped answer lists and
actual step(raw,tailValue) output once. Checked ordered answer theorem pays
slot1=tailValue in both. Build actual original layer outputs on each answers
list, stage coverage yields the same successor cache value in both tables.
Lookup functionality transports any actual first-table lookup to the second.
No manufactured table/list output or chosen semantic witness is assumed.

Different frontiers, duplicates and actual first-match precedence are allowed;
the node must actually belong to each frontier. Option None cached as zero is
not missing. This is the local base/step for a future coherence induction, NOT
a proof of global cross-root standalone-child correctness or typed definedness.
Original operators/encodings unchanged. Frozen for review, no proof yet.
