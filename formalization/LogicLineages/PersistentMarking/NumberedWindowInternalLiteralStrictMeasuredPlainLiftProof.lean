module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredParentWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredParentWindowProof (exact_OpenStrictMeasuredParentWindow)
open NumberedWindowInternalLiteralBiAuxMeasuredParentsProof (biAuxMeasuredExchange)
open NumberedWindowInternalLiteralBiAuxMeasuredLiftProof (exact_OpenMeasuredBiAuxExchangeLifts)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralMemoVaryingParentProof (varyingOperandType)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev selectedBiAuxExchange (s : Settings) (X : Program 2) (V TV baseM : Program 1) :=
  biAuxMeasuredExchange s X (unitAuxSyntax V TV) baseM chosenCombine selectedGrammarOption

abbrev selectedBiAuxWindow (s : Settings) (base : Program 2) (T V TV baseM : Program 1) :=
  strictSealedWindow (measuredStrictCover V TV baseM) s base T

abbrev selectedBiAuxPlain (s : Settings) (X base : Program 2) (T V TV baseM : Program 1) :=
  edge4 (selectedBiAuxExchange s X V TV baseM) (selectedBiAuxWindow s base T V TV baseM)

structure ParentTypeEvidence (s : Settings) (T TV : Program 1) (B : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (dom cod : OTerm α) : Prop where
  typed : D B Γ (unary T (suc z) dom ⊓ unary T (suc z) cod)
  wellFormed : D B Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)
  domain : D B Γ (memberGraph (typesTerm s α) dom)
  codomain : D B Γ (memberGraph (typesTerm s α) cod)

/-- The original typed edge itself, before installing its additional
observers, lifts at a genuine fixed operand and genuine type evidence.
Both destination windows and their syntax bits are produced in the
same proof using the selected finite grammar, not assumed of the parent. -/
theorem exact_OpenStrictMeasuredPlainLift (s : Settings) (X base : Program 2)
    (T V TV baseM : Program 1) (v : Bool) (ctx dom cod q r fixed : OTerm α)
    (types : ParentTypeEvidence s T TV B Γ dom cod)
    (arg : D B Γ (windowAt (selectedBiAuxWindow s base T V TV baseM) ctx
      (varyingOperandType (!v) dom cod) fixed))
    (arc : D B Γ (acceptEdge (selectedBiAuxPlain s X base T V TV baseM) ctx (varyingOperandType v dom cod) q r)) :
    D B Γ (acceptEdge (selectedBiAuxPlain s X base T V TV baseM) ctx cod
      (varyAuxiliary v dom cod q fixed) (varyAuxiliary v dom cod r fixed)) := by
  let X₀ := selectedBiAuxExchange s X V TV baseM
  let W := selectedBiAuxWindow s base T V TV baseM
  let p := varyAuxiliary v dom cod q fixed
  let z' := varyAuxiliary v dom cod r fixed
  obtain ⟨input⟩ := exact_OpenPackedScalarEdge X₀ W B α Γ ctx (varyingOperandType v dom cod) q r
  obtain ⟨edge⟩ := arc
  have report := Derivation.implicationElimination (Derivation.conjunctionLeft input) edge
  have raw := Derivation.conjunctionLeft report
  have qW := Derivation.conjunctionLeft (Derivation.conjunctionRight report)
  have rW := Derivation.conjunctionRight (Derivation.conjunctionRight report)
  have parent (x : OTerm α) (valid : D B Γ (windowAt W ctx (varyingOperandType v dom cod) x)) :
      D B Γ (windowAt W ctx cod (varyAuxiliary v dom cod x fixed)) ∧
      D B Γ (unary (unitAuxSyntax V TV) (suc z) (varyAuxiliary v dom cod x fixed)) := by
    cases v
    · exact exact_OpenStrictMeasuredParentWindow s base T V TV baseM ctx dom cod x fixed valid arg
        types.typed types.wellFormed types.domain types.codomain
    · exact exact_OpenStrictMeasuredParentWindow s base T V TV baseM ctx dom cod fixed x arg valid
        types.typed types.wellFormed types.domain types.codomain
  obtain ⟨⟨first⟩,u⟩ := parent q ⟨qW⟩
  obtain ⟨⟨second⟩,w⟩ := parent r ⟨rW⟩
  obtain ⟨changed⟩ := exact_OpenMeasuredBiAuxExchangeLifts s X (unitAuxSyntax V TV) baseM
    chosenCombine selectedGrammarOption v dom cod q r fixed ⟨raw⟩ u w
  obtain ⟨agree⟩ := exact_OpenPackedScalarEdge X₀ W B α Γ ctx cod p z'
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight agree)
    (Derivation.conjunctionIntroduction changed (Derivation.conjunctionIntroduction first second))⟩

#print axioms exact_OpenStrictMeasuredPlainLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
