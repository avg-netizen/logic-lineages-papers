# Next unresolved computational interface

This is a dependency map, not an accepted theorem or a frozen successor target.
It records the remaining interface after the fixed-context root-effectivity
checkpoint. No whole-source label is promoted by this note.

## Actual consumer and changing binder contexts

`NumberedTypedFocusDefinitions.TermFocus` retains `holeGamma`, `holeType`, the
typed context and selected value. `focus` enters a lambda body at
`sigma :: Gamma`. Nested lambdas and selected arguments therefore make
`holeGamma` depend on the input term and path. `NumberedStepContextsDefinitions`
provides the original `TermContext`, `ArgumentContext`, `plug` and
`plugArguments`; replacement must preserve indices, annotations and untouched
siblings exactly.

`NumberedStepCertificateDefinitions.stepTest` decodes both the replacement and
root selector at the discovered `holeGamma`, checks the replacement type against
`holeType`, invokes the original `selectorTest`, and plugs the replacement into
the original context before comparing its numeric result with the target.

The checker uses **unguarded `selectorTest`**, not `numericRootTest`. Substituting
the latter adds source-universe validation. Such a guard can be proved redundant
for a focused value from `numericStepTest` only after deriving focused universe
membership from the outer source decoder. It is not redundant for every typed
input to `stepTest`.

## Already checked reusable suppliers

`NumberedTypedValidityPrimrecProof` establishes `termSuccessPrimitive`,
`argumentsSuccessPrimitive`, `numericTermSuccessPrimitive`,
`numericArgumentsSuccessPrimitive`, `numericPackedSuccessPrimitive` and
`numericPackedValidatorPrimitive` with contexts varying jointly with their
stated raw or numeric inputs. `NumberedUniversePrimrecProof` similarly supplies
`termUniverseSuccessPrimitive`, `argumentsUniverseSuccessPrimitive` and
`rawCarrierPrimitive` jointly in windows and context. These are Boolean
success/validity computations.

The original raw type, type-list, head and structural-code parsers are already
primitive recursive. `CodeView.view`, strict `argumentEntries`, constructor
assembly, and the Position/path/StepCertificate numeric codecs are also paid.
The fixed-context dependent packed decoder and fixed-context root theorem do
not by themselves supply context-uniform computation.

## Minimal remaining route

1. Give an actual raw packed decoder returning `Option (Ty × Code (Fin n))`,
   with `Gamma` as an input. Compose the accepted parsers and joint context
   validity, and calibrate exactly to the original typed decoder followed by
   `packedCode`.
2. Compute raw focus and replacement, retaining the selected hole's context,
   type and code. Calibrate against actual `focus` and `plug`, including invalid
   paths, out-of-range indices and every permitted position. The original
   application position selects the function; it does not select the argument.
3. Supply a context-uniform computation for the original selector. The Copy
   raw operation is context independent. The present Mul interface still uses
   certificates containing `Packed Gamma`, so it needs an exact raw certificate
   presentation or equivalent uniform numeric implementation.
4. Compose these interfaces into the original `numericStepTest`, preserving
   its source-universe validation and target/type checks. Then establish the
   actual quotient-edge and positive-path certificate computations.

Arithmetic formulas for the unchanged H and positive closure R, required
source-parameter uniformity, whole-source simulation assembly and internal ID1
accessibility remain subsequent obligations. Deciding path absence is not one
of the source's required tasks.
