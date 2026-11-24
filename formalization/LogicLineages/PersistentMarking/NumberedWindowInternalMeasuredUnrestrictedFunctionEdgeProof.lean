module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow contextPresent ownSeed)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalAuxExchangeMemoLiftTargets (syntaxOne)
open NumberedWindowInternalMeasuredExchangeThinOpenChecks (exact_OpenMeasuredFactoredAuxLift)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)

private theorem syntaxFromWindow (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed : OTerm α)
    (h : Nonempty (Derivation body Γ (windowAt (window C s baseW V) ctx ty seed))) :
    Nonempty (Derivation body Γ (syntaxOne V seed)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  obtain ⟨outer⟩ := conjunctionRecover (syntaxWindow baseW V)
    (conjunction contextPresent (ownSeed C s)) xs h
  obtain ⟨inner⟩ := conjunctionRecover baseW (.composition V (fun _ : Fin 1 => .projection 2))
    xs ⟨Derivation.conjunctionLeft outer⟩
  exact compositionRecover V (fun _ : Fin 1 => .projection 2) (suc z) xs ![seed]
    ⟨Derivation.conjunctionRight inner⟩ (by
      intro n
      obtain rfl := Fin.eq_zero n
      exact projectionValue 2 xs)

/-- The exact unrestricted original measured exchange survives formation
of the same auxiliary application at two potentially distinct raw
function representatives. Parent window obligations are held; this
is not yet transport of the packed least result. -/
theorem exact_UnrestrictedMeasuredFunctionEdge (s : Settings) (base : Program 2)
    (V baseM : Program 1) (P : Program 2) (G baseW : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f g arg : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let W := window (factoredCover V M G) s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    let input := acceptEdge (edge4 X W) ctx (rawCons dom cod) f g ⊓
      (windowAt W ctx cod a ⊓ windowAt W ctx cod b)
    Nonempty (Derivation body Γ (input.imp (acceptEdge (edge4 X W) ctx cod a b))) := by
  intro M W X a b input
  let Δ := input :: Γ
  have h : Derivation body Δ input := Derivation.hypothesis List.mem_cons_self
  obtain ⟨child⟩ := exact_OpenPackedScalarEdge X W body α Δ ctx (rawCons dom cod) f g
  have x := Derivation.conjunctionLeft
    (Derivation.implicationElimination (Derivation.conjunctionLeft child) (Derivation.conjunctionLeft h))
  have ws := Derivation.conjunctionRight h
  obtain ⟨ls⟩ := syntaxFromWindow (factoredCover V M G) s baseW V body α Δ ctx cod a
    ⟨Derivation.conjunctionLeft ws⟩
  obtain ⟨rs⟩ := syntaxFromWindow (factoredCover V M G) s baseW V body α Δ ctx cod b
    ⟨Derivation.conjunctionRight ws⟩
  obtain ⟨lifted⟩ := exact_OpenMeasuredFactoredAuxLift s base V baseM P G body α Δ dom cod f g arg
  have exchanged := Derivation.implicationElimination lifted
    (Derivation.conjunctionIntroduction x (Derivation.conjunctionIntroduction ls rs))
  obtain ⟨parent⟩ := exact_OpenPackedScalarEdge X W body α Δ ctx cod a b
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
    (Derivation.conjunctionRight parent) (Derivation.conjunctionIntroduction exchanged ws))⟩

#print axioms exact_UnrestrictedMeasuredFunctionEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof
