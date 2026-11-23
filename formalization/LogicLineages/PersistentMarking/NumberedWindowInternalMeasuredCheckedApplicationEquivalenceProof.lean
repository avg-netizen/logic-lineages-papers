module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRepresentativeEqualityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastOpenIntroProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredCheckedApplicationEquivalenceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof (ParentWindowsAt)
open NumberedWindowInternalMeasuredUnrestrictedRepresentativeEqualityProof (exact_OpenMeasuredSameClassApplicationLeast)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowInternalRankCheckedLeastReportsProof (exact_OpenRankCheckedLeastReports)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem original (g : Program 1) (L : Program 3) (c ty tag out : OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (checkedLeast g L) (suc out) ![c,ty,tag]))) :
    Nonempty (Derivation B Γ (programGraph L (suc out) ![c,ty,tag])) := by
  obtain ⟨data⟩ := exact_OpenRankCheckedLeastReports g L c ty tag out held
  exact ⟨Derivation.conjunctionLeft data⟩

/-- In the actual measured checked-least physical family, both held
class representatives may differ. Their applications to the literal
same argument have identical selected class outputs, using only genuine
held open least reports and real parent windows along exchange. -/
theorem exact_OpenMeasuredCheckedApplicationEquivalence
    (s : Settings) (base : Program 2) (V baseM rank : Program 1) (P : Program 2) (G baseW : Program 3)
    (ctx dom cod f g q arg a b : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    let L := packedLeastProgram C X W s
    let K := checkedLeast rank L
    ParentWindowsAt (edge4 X W) W B Γ ctx dom cod arg →
    Nonempty (Derivation B Γ (programGraph K (suc q) ![ctx,rawCons dom cod,f])) →
    Nonempty (Derivation B Γ (programGraph K (suc q) ![ctx,rawCons dom cod,g])) →
    Nonempty (Derivation B Γ (programGraph K (suc a) ![ctx,cod,auxiliaryTerm dom cod f arg])) →
    Nonempty (Derivation B Γ (programGraph K (suc b) ![ctx,cod,auxiliaryTerm dom cod g arg])) →
    Nonempty (Derivation B Γ (eqn a b)) := by
  intro M C W X L K windows cf cg af ag
  exact exact_OpenMeasuredSameClassApplicationLeast s base V baseM P G baseW ctx dom cod f g q arg a b windows
    (original rank L ctx (rawCons dom cod) f q cf)
    (original rank L ctx (rawCons dom cod) g q cg)
    (original rank L ctx cod (auxiliaryTerm dom cod f arg) a af)
    (original rank L ctx cod (auxiliaryTerm dom cod g arg) b ag)

#print axioms exact_OpenMeasuredCheckedApplicationEquivalence
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredCheckedApplicationEquivalenceProof
