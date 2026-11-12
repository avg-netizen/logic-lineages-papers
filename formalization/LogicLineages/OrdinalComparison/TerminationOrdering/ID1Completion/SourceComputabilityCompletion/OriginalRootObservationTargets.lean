module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open OriginalRootObservation
/-- Every actual typed original root, arbitrary child observer. No source or
canonicality premise; lambda changes only its literal context component. -/
def NativeCalibration : Prop := ∀ (R : Program 2) (n : Nat) (arity : Fin n → Nat)
 (Gamma : List Ty) (c : Nat) (q : Packed (Fin n) arity Gamma),
 evaluate (rootObservation R) (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) = nativeValue R c q
/-- Explicit native specialization, conditional on the stated child observer
calibration in every context. This does not provide such a Program R or an
internal arithmetic root-signature theorem. -/
def SignatureCalibration : Prop := ∀ (R : Program 2) (n : Nat) (arity : Fin n → Nat)
 (symbols : List (Fin n)) (S : List Ty) (c : Nat),
 (∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
   evaluate R (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) = representativeCode symbols S q) →
 ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
 evaluate (rootObservation R) (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
 signatureNumber (NumberedHereditaryView.rootSignature symbols S q)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationTargets
