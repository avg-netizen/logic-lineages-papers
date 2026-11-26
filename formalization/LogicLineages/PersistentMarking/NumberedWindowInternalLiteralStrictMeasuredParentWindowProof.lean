module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredFormationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMeasuredSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredParentWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (chosenMeasure)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralMeasuredSealedWindowProof (exact_OpenFactoredSealedWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover measuredStrictWindow)
open NumberedWindowInternalLiteralStrictMeasuredFormationProof (exact_OpenStrictMeasuredFormation)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (Inputs)
open NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof (exact_OpenUnrestrictedWindowReports)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Both selected child windows produce the exact strict sealed parent.
The measured scratch and emitted syntax use the original numbered
grammar and physically agreed lexical context, which remains unchanged. -/
theorem exact_OpenStrictMeasuredParentWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let W := strictSealedWindow C s base T
    D B Γ (windowAt W ctx (rawCons dom cod) fn) →
    D B Γ (windowAt W ctx dom arg) →
    D B Γ (unary T (suc z) dom ⊓ unary T (suc z) cod) →
    D B Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod) →
    D B Γ (memberGraph (typesTerm s α) dom) →
    D B Γ (memberGraph (typesTerm s α) cod) →
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg)) ∧
      D B Γ (unary (unitAuxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)) := by
  intro C W f a intrinsic stypes inDom inCod
  let U := strictAuxWindow base T
  let M := chosenMeasure baseM
  let W' := measuredStrictWindow s base T V TV baseM
  let Va := unitAuxSyntax V TV
  let q := auxiliaryTerm dom cod fn arg
  have openAt (ty raw : OTerm α) : D B Γ (windowAt W ctx ty raw) ↔ D B Γ (windowAt W' ctx ty raw) :=
    exact_OpenFactoredSealedWindow (auxSyntax V TV) M selectedGrammarOption U s ctx ty raw
  have ready : Inputs s W' T TV B Γ ctx dom cod fn arg :=
    ⟨(openAt (rawCons dom cod) fn).mp f,(openAt dom arg).mp a,intrinsic,stypes,inDom,inCod⟩
  have parent := exact_OpenStrictMeasuredFormation s base T V TV baseM ctx dom cod fn arg ready
  obtain ⟨raw⟩ := exact_OpenUnrestrictedWindowReports C s U Va ctx cod q parent
  exact ⟨(openAt cod q).mpr parent,⟨Derivation.conjunctionLeft (Derivation.conjunctionRight raw)⟩⟩

#print axioms exact_OpenStrictMeasuredParentWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredParentWindowProof
