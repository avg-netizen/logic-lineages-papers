# Thin strict-mark field supplier, proposed only

Exact comparator: the existing frozen
`ProtectedSpineStrictTargets.MarkingFields`, with no additions or removed
premises. This quantifies the same arbitrary constructor family `M`, contexts
`Γ, Δ`, admissible assignments, source syntax and literal observations. It is
not the false arbitrary-family application equality, and adds no fixed-point
or finite-carrier membership hypothesis. The draft theorem is
`ProtectedSpineStrictMarkThinProof.exact_MarkingFields`.

The owner-host proof in `ProtectedSpineStrictMarkProof.lean` remains
byte-identical (SHA-256
`157b8a6593d891fafdd489eb75db78886f7df9645a17a8b9d549b1e039754fe1`).
Its original cloud invocation reached the fixed RSS cap, not a reported Lean
error. The new proof does not depend on its unchecked cloud object.

Two new leaves only:

- `ProtectedSpineStrictFieldLambdaStep` imports the existing strict input and
  lambda field proofs. The new local `Point` is a parameter reordering of
  exactly the frozen proposition for use as an inductive motive. A compatible
  observed lambda with an available port uses the original helper equation,
  extends the very same port context, and uses the inductive hypothesis at
  the original opened body and literally extended frame. A nonmatching
  observation, mismatched binder type or unavailable port gives both false
  fields by their definitions. The only coverage facts needed are literal
  membership in the original support's body and binder sublists; both are
  proved locally without importing the family/tuple bridge.
- `ProtectedSpineStrictMarkThinProof` invokes the generated structural
  `Expr.rec` with a trivial Arg motive because marking does not recurse into
  head lists; free and bound cases use the original strictless-input fields.
  Ordinary / marked head cases are the same definitional equality. The
  public theorem is typed against the very same frozen comparator.

Static import counts including the named leaf: original 181, new lambda
step 137, new exact theorem 138 (43 fewer than the original). The original
coverage dependency contributes 46 imports absent from the two thin bases.
No checker flags, frozen targets, manuscript, existing Lean source, or
accepted evidence have changed. Independent design review and a separate
native ticket must precede any run. Even a passed new supplier would not
certify the old adequacy roots; a later dependency cutover would be a separate
proposal with exact source identity and independent preserving review.
