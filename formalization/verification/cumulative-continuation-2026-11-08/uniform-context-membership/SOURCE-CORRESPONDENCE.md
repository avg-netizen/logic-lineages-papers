# Uniform context-only membership

Four exact targets connect the original membership semantics to a concrete context-only AST and retain the same normalized selection throughout the existing descent and canonical-fold packages. Definitions and targets were approved and frozen before any proof file existed. Their exact `.lean.txt` snapshots and SHA-256 hashes accompany this record.

## Original semantics on every raw parameter

`InternalOriginalUniformParameterLeaves.memberValue` evaluates the original membership value through the original context and Object decoders. `InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2`, proved from `JointGammaDomainCodecProof.actualObjectCodec`, supplies a decoded Object at every raw parameter and type. Its second coordinate is precisely the supplied type. Membership therefore depends only on the original context coordinate and equals its value after replacing the parameter by `Nat.pair (Nat.unpair parameter).1 0`. Malformed context codes retain the original zero result; no validity or successful-decoding assumption is introduced.

## Concrete normalized AST and internal slice

`contextMember member` sends `[type, context]` to the original binary membership program at `[type, pair(context, 0)]`. `normalizedMember member` sends `[type, parameter]` to that exact AST at `[type, left(parameter)]`. `normalizeData` replaces only the membership field, preserving the source-validity, target-validity and representative leaves literally.

The internal slice theorem starts from the actual original pairing graph `pair(context, gammaCode) = parameter`. Original pairing inversion gives the left-coordinate graph, and actual program-composition laws prove the iff between `normalizedMember(out, type, parameter)` and `contextMember(out, type, context)`. Output, parameter, context and Gamma code are arbitrary arithmetic terms. External calibration is not used as an internal reflection rule.

## Same normalized selection

The original four-leaf witness is selected once after `n` and `arity`. Its fixed syntactic normalization precedes every source window, Gamma, relation table, arithmetic body and symbolic term. The normalized tuple retains global all-input leaf calibration, the existing five internal descent laws, the four internal canonical-fold laws, and the original descent, typed, representative and whole-state-success calibrations. The retained original witness identifies the right-hand `contextMember` AST in the symbolic slice law exactly.

Uniform source/typed/vertex/path/object wrappers and the original unqualified `CertifiedApplicationLift` remain separate proof obligations. This packet does not promote a numbered statement.

## Verification scope

The exact gate `InternalOriginalUniformContextMembershipStatementChecks` passed on its first attempt in receipt `build-reports/1794172024551164344-2.json`. The four aliases `independence_exact`, `calibration_exact`, `slice_exact`, and `selection_exact` have their frozen target types and depend only on `propext`, `Classical.choice`, and `Quot.sound`. The unchanged single-thread profile used a 2048 MiB Lean heap cap, 1536 MiB process-tree RSS cap, and 2048 MiB minimum free memory. Definitions, targets, and proofs were accepted without modification.
