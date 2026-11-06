# Joint-context original partial application

Baseline: `5d17742f45314a5fabaa3eed907794061cbf38b8`. Paper06
`paper.tex` lines 570–588 uses arithmetic application in the typed arrow
computability clause. This component supplies its uniform arithmetic graph,
not C_tau assembly, closure or an internal ID1 induction proof.

The PR target names ORIGINAL NumberedNumericApplication.canonicalApplication
with Gamma inside its input. The raw helper mirrors the accepted original
applicationProgram, using calibrated raw universe/structural decoders and
representatives. Calibration must hold on all inputs and preserve every type,
universe, canonical-representative and checked-output condition.

The wrapper uses the EXISTING ContextUniform.Object decoder for function,
argument and result objects. It requires their Gamma values to agree and
calls ORIGINAL OrdinaryArithmeticApplication.applicationValue with unchanged
context, domain/codomain and payload codes. The result object is decoded,
not re-encoded: no extra canonical-encoding test is introduced. All natural
inputs, malformed codes and cross-context failures are covered.

The final target supplies an actual finite Program 6, chosen before Gamma,
with calibration on every vector. The formula is the ORIGINAL ordinary
arithmetic graph compiler applied to output one. Its all-input semantics is
the literal original decoded application lifted through the three Object
decoders. Fixed fibers and cross-context exclusion are exact. On genuine
source terms the same formula computes the original representative of
applicationPacked, under the existing subtype-closed-window premise.

Nonduplication: existing NumberedNumericApplicationPrimrecProof and
OrdinaryArithmeticApplicationProof fix Gamma before asserting PR or choosing
their formula. The accepted joint-Gamma primary, typed-carrier and other
checker components do not provide application. No accepted joint-Gamma
canonical application or same-context Object application graph was found.
Existing raw decoder/representative and fixed-Gamma calibration theorems are
suppliers, not substitute application semantics.

New definitions/targets and original source hashes are frozen before proofs.
Preflight, exact aliases, native source matching and standard-axiom audits
use unchanged serialized caps. No existing source/target, manuscript, register,
checker, dependency, root import or CI changes. No C_tau, internal ID1
derivability, accessibility, well-foundedness, whole lem:id1 or II5 claim.
