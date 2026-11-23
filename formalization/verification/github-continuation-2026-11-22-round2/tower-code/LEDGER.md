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
