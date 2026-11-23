# Paper 16: first four literal native tower witnesses and actual finite-prefix folding

The printed source is the sequence (D) at `ordinals.tex:563–572` and the
literal replacement convention (t_n) at :584–591. `level` is the printed
finite type ladder (A_0=ι), (A_{i+1}=A_i→A_i). `ty` translates using the
original `NativeIndexedCarrierTargets.actualType` so (A_0) has actual native
type `o→o`. The same actual prefix heads already checked in #1463 are used,
not terms selected for extensional or ordinal reasons.

| Output | Exact original left-associated raw expression |
|---|---|
| `t0` | `nativeNB omegaCarrier` |
| `t1` | `nativeNB t0` |
| `t2` | `(extractorZero nativeNB) t0` |
| `t3` | `((extractorOne extractorZero) nativeNB) t0` |
| `later prefix` | `((B_l B_(l−1) … B₀) nativeNB) t0` with supplied literal raw operands; no claim they are automatically the printed extractors |

Every juxtaposition is the original `NativeReduction.app` with exact typed
input and output fields. The high-to-low fold uses a single actual head of
type (A_{k+3}=A_{k+2}→A_{k+2}) then the genuine closed next operand at
(A_{k+2}). `ClosedPrefix.lower` returns the actual original typed, ordinary,
closed native term at (A_2); erasing the proof objects is the exact raw
left-spine fold, not a new evaluation or normalization. Original closed
application installs `nativeNB` and then the literal `t0`. No independently
claimed totality for arbitrary ill-typed raw prefixes. The four explicit
terms form a separate unconditional instance for each actual signature.

The actual right-operand Select rule gives `t0 ≻c omegaCarrier`,
`t1 ≻c t0`, and `t2 ≻c t0`, `t3 ≻c t0`; every same typed supplied-prefix
instance of `later` also has the literal `t0` as a strict endpoint.
No claim that `t3 ≻c t2` or that the sequence itself is a strict chain.

Raw codes in this packet are original `Spine.Expr`; no natural codec or
effectivity claim beyond the structural source functions. Constructing
a uniform actual code for every printed (B_l) beyond the checked (B₀,B₁)
is a separate step. No ordinal interpretation, collapse calibration,
cofinality, or numbered promotion. Native gate:
`LogicLineages.PersistentMarking.NativeTowerWitnessPrefixProof`, six
explicit axiom reports.
