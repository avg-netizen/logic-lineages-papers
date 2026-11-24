# Paper 16: a checked functional union for literal J

The fixed unary repacker decodes the original scratch list and rebuilds
the literal sparse raw cells. Its all-input numerical calibration includes
the unchanged decoder fallback and a two-cell regression: scratch [2,3]
repackages to raw code 228. The internal graph proof is separate from
the numerical calibration. Object-list induction constructs both the
fixed repacker graph and the original positive parser graph for the same
output. Graph functionality identifies that witness with any held output.

The binary functional union feeds the two original parser payloads to
the original scratch append, then repacks. For two positively parsed
inputs, its held graph supplies the old certified union at that same raw
output using reflexivity of the literal permutation observer. Carrier
extraction and arithmetic parser opening give those two inputs for J.
This proves `ConditionalJUnionTargets.UnionClosure` for the actual
`literalData i r`, rather than only for an abstract `Program 2`, with no
new arithmetic or splitting assumption. It does not identify arbitrary
accepted permutations with the chosen ordered output or prove the
different functional `MultisetSplit` condition. No numbered promotion.

The named theorem outputs contain only the permitted standard axioms.
The adjacent archive contains successful source rows, exact raw receipts
and named logs; some earlier attempts in those same receipts fail on a
later module, and are identified separately. The final exact combined
gate uses the checker's hash-validated local object cache for unchanged
rows. No full project CI pass is implied.
