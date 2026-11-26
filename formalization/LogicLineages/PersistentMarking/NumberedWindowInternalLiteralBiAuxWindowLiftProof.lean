module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredParentWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMeasuredLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxWindowLiftProof
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

open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (ParentTypeEvidence selectedBiAuxExchange)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow exact_OpenJoinedAuxiliaryParent)

def AuxWindowAssembly (s : Settings) (T TV Va : Program 1) (W : Program 3) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    ParentTypeEvidence s T TV B Γ dom cod →
    D B Γ (windowAt W ctx (rawCons dom cod) fn) → D B Γ (windowAt W ctx dom arg) →
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg)) ∧
      D B Γ (unary Va (suc z) (auxiliaryTerm dom cod fn arg))

abbrev joinedBiAuxPlain (s : Settings) (X base : Program 2) (T V TV baseM : Program 1) :=
  edge4 (selectedBiAuxExchange s X V TV baseM) (joinedAuxiliaryWindow s base T V TV baseM)

theorem exact_OpenJoinedWindowAssembly (s : Settings) (base : Program 2) (T V TV baseM : Program 1) :
    AuxWindowAssembly s T TV (unitAuxSyntax V TV) (joinedAuxiliaryWindow s base T V TV baseM) := by
  intro B α Γ ctx dom cod f a types fn arg
  exact exact_OpenJoinedAuxiliaryParent s base T V TV baseM ctx dom cod f a types fn arg

/-- Only an explicit, actual old-window formation law is needed for
either typed position, before the original observer suite is installed. -/
theorem exact_OpenBiAuxWindowLift (s : Settings) (X : Program 2)
    (T V TV baseM : Program 1) (W : Program 3)
    (formed : AuxWindowAssembly s T TV (unitAuxSyntax V TV) W) (v : Bool) (ctx dom cod q r fixed : OTerm α)
    (types : ParentTypeEvidence s T TV B Γ dom cod)
    (arg : D B Γ (windowAt W ctx
      (varyingOperandType (!v) dom cod) fixed))
    (arc : D B Γ (acceptEdge (edge4 (selectedBiAuxExchange s X V TV baseM) W) ctx (varyingOperandType v dom cod) q r)) :
    D B Γ (acceptEdge (edge4 (selectedBiAuxExchange s X V TV baseM) W) ctx cod
      (varyAuxiliary v dom cod q fixed) (varyAuxiliary v dom cod r fixed)) := by
  let X₀ := selectedBiAuxExchange s X V TV baseM
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
    · exact formed B α Γ ctx dom cod x fixed types valid arg
    · exact formed B α Γ ctx dom cod fixed x types arg valid
  obtain ⟨⟨first⟩,u⟩ := parent q ⟨qW⟩
  obtain ⟨⟨second⟩,w⟩ := parent r ⟨rW⟩
  obtain ⟨changed⟩ := exact_OpenMeasuredBiAuxExchangeLifts s X (unitAuxSyntax V TV) baseM
    chosenCombine selectedGrammarOption v dom cod q r fixed ⟨raw⟩ u w
  obtain ⟨agree⟩ := exact_OpenPackedScalarEdge X₀ W B α Γ ctx cod p z'
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight agree)
    (Derivation.conjunctionIntroduction changed (Derivation.conjunctionIntroduction first second))⟩

#print axioms exact_OpenJoinedWindowAssembly
#print axioms exact_OpenBiAuxWindowLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxWindowLiftProof
