module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedRawFunctionLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoAuxParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityTypingProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
  (joinedAuxiliaryWindow exact_OpenJoinedAuxiliaryWindow)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof
  (selectedJoinedRaw exact_OpenSelectedJoinedRawWindows)
open NumberedWindowInternalLiteralCoveredMemo (coveredIntrinsic coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (actualAuxChildren childAtWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxParentProof (exact_OpenCoveredMemoAuxParent)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRawTransport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- If the actual beta target is the literal replacement, its checked
type is the original auxiliary argument's type. Both type results
come from the same covered intrinsic computation. -/
theorem exact_OpenIdentityBetaTypeFromHop
    (s : Settings) (base : Program 2) (T V TV baseM i cv tv : Program 1)
    (leaf : Nat → Program 3) (other L : Program 3)
    (ctx ty before cert after q w r dom cod fn arg : OTerm α)
    (checked : D B Γ (hopCalls
      (rawWithTarget i cv tv (selectedJoinedRaw s base T V TV baseM leaf other) L)
      L ctx ty before cert after q w r))
    (source : D B Γ (eqn q (auxiliaryTerm dom cod fn arg)))
    (output : D B Γ (eqn r arg)) : D B Γ (eqn ty dom) := by
  let raw := selectedJoinedRaw s base T V TV baseM leaf other
  let Q := joinedAuxiliaryWindow s base T V TV baseM
  let C := measuredStrictCover V TV baseM
  let Va := unitAuxSyntax V TV
  let W := coveredMemoWindow C s base T Va
  let F := coveredIntrinsic C s base T Va
  let src := auxiliaryTerm dom cod fn arg
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  obtain ⟨report⟩ := checked
  have physical : D B Γ (programGraph (rawWithTarget i cv tv raw L) (suc z) xs) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight report)⟩
  obtain ⟨rawReport⟩ := conjunctionRecover raw (targetGate i cv tv L) xs physical
  obtain ⟨sourceWindow,targetWindow⟩ := exact_OpenSelectedJoinedRawWindows s base T V TV baseM
    leaf other ctx ty q w r ⟨Derivation.conjunctionLeft rawReport⟩
  have sourceShaped : D B Γ (windowGraph Q ctx ty src) :=
    windowRawTransport Q ctx ty q src source sourceWindow
  obtain ⟨_,sourceMemo⟩ :=
    (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty src).mp sourceShaped
  obtain ⟨_,targetMemo⟩ :=
    (exact_OpenJoinedAuxiliaryWindow s base T V TV baseM ctx ty r).mp targetWindow
  obtain ⟨children⟩ := exact_OpenCoveredMemoAuxParent C s base T Va ctx ty dom cod fn arg sourceMemo
  unfold actualAuxChildren childAtWindow at children
  have argMemo : D B Γ (windowGraph W ctx dom arg) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight
      (Derivation.conjunctionRight (Derivation.conjunctionRight children)))⟩
  have retaped : D B Γ (windowGraph W ctx ty arg) :=
    windowRawTransport W ctx ty r arg output targetMemo
  have targetTyped := (exact_OpenIntrinsicQuery F B α Γ ctx ty arg).mp retaped
  have argTyped := (exact_OpenIntrinsicQuery F B α Γ ctx dom arg).mp argMemo
  obtain ⟨same⟩ := valueUnique F (suc ty) (suc dom) ![ctx,arg] targetTyped argTyped
  exact ⟨cancelSuc same⟩

#print axioms exact_OpenIdentityBetaTypeFromHop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaIdentityTypingProof
