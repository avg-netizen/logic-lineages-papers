module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationTargets
open Source DecodedSourceCalibration
open InternalOriginalUniformDescentSelection (Data)

/-- The globally calibrated ORIGINAL Data precedes every raw parameter.
Successful Context decoding does NOT assert that the supplied raw context
is its re-encoding. One original Gamma supplies the whole unrestricted raw
value/type/application slice. The source-window subtype closure is the only
mathematical window premise; no typedness, N-fixedness, successful result,
nonzero value or canonical-input premise restricts any numeric conclusion.

This pays a native decoded-window prerequisite for the later ALL-input
outer assembly. It does not calibrate malformed-context fallback dispatch,
assert resultOption success, select a source package, or reflect a native
equality into an internal arithmetic derivation. -/
def ActualDecodedCompositeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (d : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity d →
  ∀ (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode (Nat.unpair parameter).1 = some ctx →
  SubtypeClosed (fun typ => typ ∈ ctx.1.2) →
  ∃ Gamma : List Ty, DecodedCalibration n arity d parameter ctx Gamma

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationTargets
