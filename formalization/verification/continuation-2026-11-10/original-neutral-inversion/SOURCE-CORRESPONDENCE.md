# Source correspondence — original neutral inversion

The source is `06-godel-t-termination-ordering/paper.tex`, `lem:id1` at line558.
The relevant paragraph at lines582–590 uses the fact that a non-lambda
application reduces only on its function side or to bottom. The paper works
on least-code primary-equivalence representatives. This checkpoint completes
the original raw certificate/checker argument needed before quotient transport.
The registered full lemma remains pending.

## Actual supplied certificate

`NumberedNonLambdaApplicationProof.actualNonLambdaApplicationStep` describes
semantic reduct shapes but does not identify the certificate accepted by a
numeric checker. The new typed inversion inspects that certificate's own
focus path. An empty path supplies an actual root rule, whose non-lambda
application case is bottom. A nonempty accepted application path must start
with the original `appFunction` position. Its literal suffix, replacement
number and root selector form the child certificate, and the existing exact
typed lift equation pays child acceptance.

The numeric inversion decodes the supplied certificate once and recovers its
original code using the decoder's soundness and the actual step encoding.
It proves equality with `liftStep child`; certificate completeness never
substitutes another witness. No subtype-closure or confinement premise is
added to either inversion. Numeric acceptance supplies the required typed
source and its universe membership.

## Actual child validity and step acceptance

The inherited accepted-guard inversion recovers complete original application
and endpoint witnesses and the selected child checker. That endpoint provides
only packed validity at the target function. The complete `stepChecker`
also requires source-universe validity there.

The new validity proof obtains both child fold outputs internally, reverses
the existing actual application-fold equation, recovers the three accepted
combine factors, and uses Program functionality to identify each child output
with one. It applies this to both the packed and universe folds, rebuilding
source validity at both children. Applied to the accepted target application,
this pays the missing target child source-validity. The same complete
`stepChecker` is then reconstructed at the child, with its original
function/target/certificate/parameter inputs.

## Concrete neutral old-leaf refinement

`OriginalNeutralLeaf.neutralTest` checks the original raw application tag and
the actual function payload's non-lambda tag. The added trigger conjoins the
existing Context-window test, that neutral test, and zero acceptance of the
actual parameterized guard on the original edgeCode. Only its triggered
branch requires equality of the actual target with the literal same-type
`BottomRepresentative.bottomCode`. The old leaf remains an acceptance factor.

Two separate proofs pay this construction. Internally, concrete Program
graph and branch rules give the old factor and same-type bottom law for
arbitrary leaves, endpoints, contexts and symbolic inputs. Externally,
original leaf calibration supplies its zero/one output on every raw input.
On accepted active inputs, the original Context decoder and window test
recover a closed window and an arbitrary-parameter endpoint slice. The new
supplied-certificate inversion leaves only bottom: its function alternative
would make that same guard accept at one, contradicting its actual zero
value. Inactive, rejected and malformed inputs retain the original output.
No external calibration theorem becomes an internal derivation rule.

## One source before all windows

Starting from one original globally calibrated tuple `p`, the construction
forms `q := OriginalNeutralLeaf.refineInputs p` and then
`r := OriginalVariableRepresentative.refineInputs q`. All-input calibration
survives both changes. The endpoint depends on the unchanged validity/member
fields and is literally the original neutral endpoint. The constructor
refinement retains `q.oldStep` as an actual internal acceptance factor, so
the neutral bottom law survives at `r.oldStep`.

The complete Package, variable certificate-bottom law and variable-I laws
are instantiated for this same final `r`, after selection and before arbitrary
source windows. No fresh source is chosen for different constructors, windows
or Gamma values. The final raw neutral-step elimination combines the full
selected-step split with this paid neutral law, discharging its leaf branch.

## Remaining quotient boundary

The actual quotient edge may start from a raw representative of an application,
rather than that application itself. Today's raw result does not show that
this representative has the required application components or non-lambda
function. Native primary-equivalence shape theorems cannot be reflected into
the arithmetic calculus. The next proof must recover those facts internally
for the same full canonical fold, or supply an all-input-calibrated global
refinement that makes the needed internal laws derivable.
