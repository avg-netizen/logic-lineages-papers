module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuard
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedBottomAccessibilitySupportProof NumberedBottomSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only proper original typed packed terms are required here. Acceptance
of an old edge supplies those terms for EVERY raw numeric endpoint; this is
not a successful-decoding restriction on the calibration conclusion. -/
def ShapeCalibrated (n : Nat) (arity : Fin n → Nat) (bottom measure : Program 1) : Prop :=
  ∀ (Gamma : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
  let value := packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma)
  (evaluate bottom (List.Vector.ofFn ![value]) = 1 ↔
    (bottomView (⟨tau,q⟩ : Packed (Fin n) arity Gamma)).isSome = true) ∧
  (((Nat.unpair (evaluate measure (List.Vector.ofFn ![value]))).1 = 1 ↔ BottomSpine q) ∧
    (Nat.unpair (evaluate measure (List.Vector.ofFn ![value]))).2 = spineDepth q)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuard

namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardTargets
open Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The stronger literal positive checker retains the ORIGINAL positive
test on ALL natural endpoints and path codes at any calibrated parameter.
No endpoint typing, successful decode, canonical-input or type-membership
hypothesis is added. The guard Programs precede every finite window/Gamma. -/
def ActualOriginalAllInputPositiveGuardCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (bottom measure : Program 1) (edge : Program 4),
  PositiveGuard.ShapeCalibrated n arity bottom measure →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (parameter : Nat),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalParameterizedPathChecker.EdgeCalibrated n arity symbols S Gamma table edge parameter →
  ∀ (x y certificate : Nat),
  evaluate (PositiveGuard.checker bottom measure edge)
      (List.Vector.ofFn ![x,y,certificate,parameter]) =
    if NumberedQuotientPathCertificates.positivePathTest n arity symbols S Gamma table x y certificate
      then 1 else 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardTargets
