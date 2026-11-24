module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique equalEqn programRename)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRawListRecursionSyntaxProof (recRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm Zero)
open NumberedWindowInternalDirectInsertedRowCasesTargets (Reports)
open NumberedWindowInternalDirectInsertedRowCases (exactOpenInsertedRowCases)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep)
open NumberedWindowInternalOpenOriginScanRoutedStepProof (exact_OpenOriginScanRoutedStep)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOpenOriginScanRoutedHeadTargets

attribute [local irreducible] programGraph
local notation "T" => OrdinaryArithmetic.Term
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem poolMember (raw old fixed dom : T α)
    (oldReport : D B Γ (unary parser (suc old) raw))
    (fixedReport : D B Γ (unary parser (suc fixed) raw))
    (mem : D B Γ (programGraph scratchMember oneTerm ![old,dom])) :
    D B Γ (programGraph scratchMember oneTerm ![fixed,dom]) := by
  obtain ⟨same⟩ := valueUnique parser (suc old) (suc fixed) ![raw] oldReport fixedReport
  unfold programGraph at mem ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula scratchMember)
    oneTerm ![old,dom] ![fixed,dom] _ mem
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change D B Γ (equal old fixed)
    rw [equalEqn]
    exact ⟨cancelSuc same⟩
  · obtain rfl := Fin.eq_zero j
    change D B Γ (equal dom dom)
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl dom⟩

private theorem pin {r : Program 3} {raw row old fixed tgt dom cert : T α}
    (ps : D B Γ (unary parser (suc fixed) raw))
    (reports : Reports r B Γ raw row old tgt dom cert) :
    Reports r B Γ raw row fixed tgt dom cert := by
  refine ⟨ps,reports.targetField,reports.dominatorField,reports.certificateField,?_⟩
  obtain ⟨report⟩ := reports.original
  have rest := Derivation.conjunctionRight report
  obtain ⟨m⟩ := poolMember raw old fixed dom reports.parsed ps ⟨Derivation.conjunctionLeft rest⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft report)
    (Derivation.conjunctionIntroduction m (Derivation.conjunctionRight rest))⟩

private theorem singletonRename {β : Type} (p : T α) (j : α → β) :
    (fun i : Fin 1 => ((![p] : Fin 1 → T α) i).relabel j) = ![p.relabel j] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem loopRename {β : Type} (r : Program 3) (code removed : T α) (j : α → β) :
    (loopAccept r code removed).relabel j = loopAccept r (code.relabel j) (removed.relabel j) := by
  simp only [loopAccept, recRename, singletonRename, oneTerm, sucRelabel, zRelabel, NumberedWindowInternalDirectInsertedRowTargets.Zero]

/-- Recover the original row witness in the actual strengthened object
context, pin it to the fixed parsed removed tape, and use the two
concrete filter step runs to build the side-local scans. -/
theorem exact_OpenOriginScanRoutedHead : ExactOpenOriginScanRoutedHead := by
  intro r B α Γ removed decoded row rawLeft rawRight scratchLeft scratchRight
    joined tailLeft tailRight outLeft outRight accepted parsed parseL parseR count app leftOK rightOK stepL stepR
  let goal := loopAccept r outLeft rawLeft ⊓ loopAccept r outRight rawRight
  apply exactOpenInsertedRowCases r B α Γ removed row goal accepted
  intro β j Δ actual tgt dom cert keep reported
  have parsed' := renameParser removed decoded parsed j Δ keep
  have parseL' := renameParser rawLeft scratchLeft parseL j Δ keep
  have parseR' := renameParser rawRight scratchRight parseR j Δ keep
  have count' := renamePair permutation (suc z) decoded joined count j keep
  have app' := renamePair append joined scratchLeft scratchRight app j keep
  have leftOK' := renameInto leftOK j Δ keep
  have rightOK' := renameInto rightOK j Δ keep
  have stepL' := renameInto stepL j Δ keep
  have stepR' := renameInto stepR j Δ keep
  rw [loopRename] at leftOK' rightOK'
  simp only [programRename,tripleInputsRename] at stepL' stepR'
  simp only [sucRelabel,zRelabel] at count'
  simp only [goal,conjunctionRename,loopRename]
  exact exact_OpenOriginScanRoutedStep r B β Δ (removed.relabel j) (decoded.relabel j)
    (row.relabel j) tgt dom cert (rawLeft.relabel j) (rawRight.relabel j)
    (scratchLeft.relabel j) (scratchRight.relabel j) (joined.relabel j)
    (tailLeft.relabel j) (tailRight.relabel j) (outLeft.relabel j) (outRight.relabel j)
    (pin parsed' reported) parseL' parseR' count' app' leftOK' rightOK' stepL' stepR'

#print axioms exact_OpenOriginScanRoutedHead

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
