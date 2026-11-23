# Native tower code ledger — client date 2026-11-22 (America/Chicago)

## Preproof freeze

UTC timestamp: 2026-11-23T03:57:18.401748+00:00

Reviewed base: `b28541e6f1682fc41c47a385729df36e9db87b0d`. The following exact definitions, target, and source map were frozen before creating the proof module. Native validation is pending the root-owned gate; no compiler was run in this lane.

| File | SHA-256 |
|---|---|
| `LogicLineages/NativeModule/PersistentMarking/NativeTowerCodeDefinitions.lean` | `f2ca242c37f927536b951fdd02e526bb40e43cee8f9d2e7d738e48e7cc5b4f36` |
| `LogicLineages/NativeModule/PersistentMarking/NativeTowerCodeTargets.lean` | `afeffe985c1d705c185cb5e4e7967257f78d0847973c1a2c0e1e0fa7739de079` |
| `verification/github-continuation-2026-11-22-round2/tower-code/SOURCE-MAP.md` | `330aed1d00385c7281cbe808537e8a80a1d2fec0e7521fd52994326ffe0e1ece` |

The target is unconditional primitive recursiveness of the concrete `sequenceCode`, successful exact calibration to `tr` followed by `encodeTerm`, and equality to the existing `nativeCode` on the explicit native tower family. No external ordinal or accessibility hypothesis is used.

## Proof draft ready for root gate

UTC timestamp: 2026-11-23T04:00:55.103204+00:00

`LogicLineages/NativeModule/PersistentMarking/NativeTowerCodeProof.lean` SHA-256 `36f70ff5fabe0145219896ae97a7fed6085b2b075777c19b6ef4ce4ad11aea78`. Public aliases: `sequenceCodePrimitiveRecursive`, `sequenceCodeComputable`, `sequenceCodeCalibration`, `nativeCodeCalibration`, `fullTowerCode`. The proof uses numerical primitive recursion/bounded iteration and exact constructor-by-constructor translation calibration. No compiler has been run in this lane; native outcome remains pending.

## Native gate 02: proof-only repair

UTC timestamp: 2026-11-23T04:11:40.924611+00:00

Root reports gate 01 accepted the frozen Definitions and Targets unchanged. Gate 02 (`build-reports/1795407001183373242-11.json`; full log `../root/logs/native-gate-02.log`) accepted the primitive-recursiveness alias with standard axioms but rejected the proof module. The exact first proof draft was preserved at `drafts/NativeTowerCodeProof-v1-gate02.lean.txt`, SHA-256 `36f70ff5fabe0145219896ae97a7fed6085b2b075777c19b6ef4ce4ad11aea78`.

Repairs: import the existing Partrec/Computable interface, simplify Option translation binds with the full simp set, correct successor-branch layout, and unfold the literal binder/fix/sequence equations and index-type encoding explicitly during calibration. Definitions, target, and source-map freezes remain unchanged. Revised proof SHA-256 `604729d8749a64b9446c0c36acae2b363361efcb25b10b765e226401c07ff66d`; root native regate pending. No compiler was run in this lane.

## Native gate 05: public import repair

UTC timestamp: 2026-11-23T04:13:02.457307+00:00

Root reports receipt `build-reports/1795407148774081979-11.json` has one remaining module error: the public computability alias requires a public Partrec import. The calibration and full-target axiom outputs are now standard-only. Preserved proof SHA-256 `604729d8749a64b9446c0c36acae2b363361efcb25b10b765e226401c07ff66d` in `drafts/NativeTowerCodeProof-v2-gate05.lean.txt`. Changed only `import Mathlib.Computability.Partrec` to `public import Mathlib.Computability.Partrec` in the proof. Current proof SHA-256 `72a7f247b4371779f7d08522c5a103072a9c215bcc4444179593a997722ca3bd`; root native regate pending. Frozen definitions, target, and source map remain unchanged.

## Native gate 06 — PASS; packet accepted as #1476

UTC timestamp: 2026-11-23T04:14:04.344060+00:00

Root reports native receipt `build-reports/1795407211156632997-11.json` passed `NativeTowerCodeProof` and the downstream coded main integration. All five coding aliases compiled successfully: `sequenceCodePrimitiveRecursive`, `sequenceCodeComputable`, `sequenceCodeCalibration`, `nativeCodeCalibration`, and `fullTowerCode`. Axiom outputs are standard-only: the calibration aliases use `[propext, Quot.sound]`; the primitive-recursive/computable/full aliases use only `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or additional axiom remains in the accepted module.

Accepted proof SHA-256: `72a7f247b4371779f7d08522c5a103072a9c215bcc4444179593a997722ca3bd`. Root accepts this supporting packet as #1476. The Definitions, Targets, and source-map hashes remain the preproof freezes above. Both failed proof drafts are retained. No numbered Paper 16 theorem is promoted by this packet; the unconditional result is exact primitive-recursive generation of the existing native tower codes. Conditional ordinal/cofinality assumptions remain in the separate integration target. No further authoring is planned in this lane.
