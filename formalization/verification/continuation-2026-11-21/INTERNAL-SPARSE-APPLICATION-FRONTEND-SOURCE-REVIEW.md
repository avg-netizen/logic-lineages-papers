# Paper 16: next physical application frontend (source review only)

This is source planning after the six-coordinate output-core target
preflight. It does not freeze a third proof lane or attest any new
proof. Original manuscript and selected source body are unchanged.

## Original executable, down to each guard

`NumberedWindowAddressApplication.application` first decodes *both*
whole inputs using the original `addressView`. Its `applyAddresses`
then decodes the source result type via the real `arrowView` and
requires the two original canonical bits, equality of the **ordered**
decoded contexts (with repeats), and equality of the arrow domain
with the argument's result type. It builds the tag-six raw seed from
[domain,codomain,sourceLeast,argumentLeast], calls least at the original
ordered context/codomain, and emits tag three with the repacked
context, codomain, and returned code. The original graph compares that
optional output to `some y`. There is **no** independent output scalar
admission check in this code.

At the numerical level the same installed `i` from the actual
`Evaluates (checks entries s) i j r d` provides both successful-view
and canonical checks on each whole input: the literal original
`scalar s n = (addressView n).any (canonical s)`, not a call on a raw
least field, not the separately selected typed scalar. See
`NumberedWindowInternalSparseTupleApplicationProof.guardedValue`
for the same two numerical guards with the old physical calibration.
This is not open inversion of an arbitrary primitive computation.
Both actual shape guards and their selector graphs must be physical
separate branches for a source-exact open report.

## Reusable exact leaves

- `NumberedWindowInternalSparseAddressPositiveNumericShapeProof`:
  `viewDecoded`, `decodedView`, `sameContext`. Literal packed
  equality is equivalent to equality of the two decoded ordered
  lists **after** the actual successful context views; equality
  alone does not imply either parse. Repacking successful field lists
  uses the exact original codec law. Do not sort or deduplicate.
- `NumberedWindowInternalFreshProbeParsedEmitterAddressProof`:
  `addressCoordinates` at each input; `chosenArrow`,
  `arrowMissing`, and `exactCoordinates` for all raw source-result
  parser outcomes. The argument may be ground: no argument-arrow
  premise. Domain comparison is source raw domain vs argument raw
  result.
- `NumberedWindowInternalFreshProbeParsedEmitterObjectChecks`:
  `exact_OpenAddressArrowCoordinates` provides the actual literal
  node and arrow terms from real tag-three/source-arrow graphs.
  `NumberedWindowInternalSparsePathEnvelopeOpenNodeProof.readNode`
  and `packedNode` supply the argument shell.
- `NumberedWindowInternalSparseAddressPositiveOpenMatchProof.readSame`
  and `introSame` illustrate the same selector on two addresses.
  Domain/result uses two different physical projections; use the
  arithmetic equality graph eliminator and introducer rather than
  pretend it is that same-selector case.

## Minimal next contract

Select a physical arity-three guarded program on [f,u,y] that uses
that same `i` once on each endpoint and the actual tag-three guards,
source arrow guard, packed-context comparison and domain comparison,
then composes the actual output core on
[sourceContext,sourceDomain,sourceCodomain,sourceLeast,argumentLeast,y].
Prove separate all-raw original graph calibration under the named
actual scalar and least calibrations, and genuine arbitrary-open
equivalence to a shared-coordinate report in the same body/context.
The report retains real scalar and shape witnesses at both endpoints,
a single shared context/domain, the original application seed, and the
same actual least/output witness. Numerical reject branches cover all
malformed inputs. `Closed K`/`ValidWindow` are not required solely
for this calibration; use stronger hypotheses only where a subsequent
window/carrier lemma actually needs them.

Do not identify the old physical `p₀` or `guard i p₀` with this
program by value equality. Replacing selected application in an
installed tuple, output scalar admission, symbolic argument-fiber
reports, original least/congruence matching, and object accessibility
are separate. The exact `RawMatching` input has only `r f w g`
and `p g u v`; it does not assume a supplied earlier application,
an output carrier, bare term shape, or identical raw argument fields
after quotient canonicalization. Both the earlier result and its
transformed path certificate must actually be bound in that calculus.

**Preserve the installation shape in the design.** Let the new core
frontend `p₀` contain the shape/selector/equality/output leg only, and
let the final physical `p` be the existing `guard i p₀` from
`NumberedWindowGuardedGraphTargets` (its slot-0/unit and slot-1/unit
conjunctions are exactly the two actual scalar guards). Prove
all-input calibration for `guard i p₀`, not for the unguarded p₀.
The new `p₀` can reject shapes without checking canonicality;
it need not equal the old independently chosen numeric p₀. This
placement avoids doubling the i checks and keeps the existing shape
`v.applicationGuard = guard i p₀` available in a subsequent literal
fresh tuple construction. Any uniqueness of new p₀ needed by the
old guard helper requires separate open object functionality; final
guarded uniqueness can instead align sufficient report witnesses
on the two unchanged inputs using exact graph functionality.
