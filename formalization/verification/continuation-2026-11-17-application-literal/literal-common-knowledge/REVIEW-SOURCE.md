# Independent candidate source review — literal common knowledge

2026-11-17. **Source semantics accepted; native proof gate pending.**
This is a source-first checkpoint review, not final mathematical adoption.
The Bool-strengthened target/comparator pins in `REVIEW-PREFLIGHT.md` remain
unchanged.

## Candidate pins

Under `LiteralCommonKnowledgeCounterexample/`:

- `CollapseProof.lean`: `a45f39ef7bae05d087ab303722b92013eb6905f546cb20d7df936c4ff40425c7`.
- `KTTransportProof.lean`: `8313092fcf647752ab07d793d6dbd5dbb182c3bc1bbe5c10aff91c4a4e7116ca`.
- `Proof.lean`: `fcde14f35612436f61855ca5e87988f7da0ee27c5bff184a143705d5e9d54f52`.
- `StatementChecks.lean`: `487faf5e0fda195d78eb6587cd15b61b272b78340ecbc3899c47b662a7df9ef8`.

The collapse proof derives the original guarded-source collapse from internal
HB at the supplied tuple, then composes it with checked chosen-CK transport
for the displayed literal formula. It never identifies the two formula codes.

The structural KT embedding preserves the six original proof constructors.
Ordinary blocks use original axiom inclusion; false-only Barcan is impossible.
The theorem-only rules retain global theorem premises. Literal negation uses
ordinary collapse to derive `C → E`, the existing KT theorem `E → b`, and
the arithmetic theorem `¬b`. The local assumptions in the ordinary
implication-to-negation helper are discharged before use in KT.

For each Bool flag, the proof retains literal theta, its actual chosen-CK
negation, every external finite iteration, and nonprovability. The final
contradiction invokes the existing actual-KT consistency theorem at that
same flag and tuple. The selected-presentation consumer destructs one
original witness and retains every registry, syntax, fixed-point, and HB
field. No new consistency or source-oracle premise is introduced.

The packet contains seven candidate proof theorems and three exact aliases.
Comparator preflight passed in coordinator receipt
`build-reports/1794956385081898391-5.json`. The 300-module candidate closure
still requires its native gate, standard-axiom audit, and evidence
reconciliation. The selected-presentation antecedent is explicit here;
unconditional installed-source acceptance belongs to the separate packet.
The reviewer ran no compiler or Git operation.
