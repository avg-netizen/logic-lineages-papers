module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapAcceptedConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets targetBase targetStep)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept rowAccept)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanCons)
open NumberedWindowInternalDirectInsertedRowCases (exactOpenInsertedRowCases)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectTargetMapIntroSyntaxProof
  (projectedRename hasRename projectionIntro projectionCases)
open NumberedWindowInternalDirectTargetMapLocalIntroProof (exact_OpenTargetProjectionStepIntro)
open NumberedWindowInternalDirectTargetMapIntroTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeTwo (a b : OTerm α) :
    (![a,b] : Fin 2 → OTerm α) = Fin.cons a (Fin.cons b Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem finishHead (rows row tail target prior : OTerm α)
    (cell : D B Γ (consGraph rows row tail))
    (tag : D B Γ (unary (guardAt 4) (suc z) row))
    (view : D B Γ (unary (field 0) target row))
    (tailProjected : D B Γ (unary scratchTargets (suc prior) tail)) :
    D B Γ (hasProjection rows) := by
  apply programCases consCode ![target,prior] (hasProjection rows)
  intro β j Δ out keep targetCons
  rw [binaryInputsRename] at targetCons
  have input := renameInto cell j Δ keep
  rw [consGraphRename] at input
  have tag' := renameInto tag j Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at tag'
  have view' := renameInto view j Δ keep
  rw [unaryRename] at view'
  have tail' := renameInto tailProjected j Δ keep
  rw [projectedRename] at tail'
  have own : D B Δ (consGraph out (target.relabel j) (prior.relabel j)) := by
    simpa only [consGraph,tapeTwo] using targetCons
  have step := exact_OpenTargetProjectionStepIntro B β Δ (row.relabel j)
    (target.relabel j) (prior.relabel j) out tag' view' own
  have step' : D B Δ (programGraph targetStep (suc out)
      (Fin.cons (row.relabel j) (Fin.cons (suc (prior.relabel j)) Fin.elim0))) := by
    simpa only [tapeTwo] using step
  have report : D B Δ (unary scratchTargets (suc out) (rows.relabel j)) :=
    consValue targetBase targetStep (rows.relabel j) (row.relabel j) (tail.relabel j)
      (suc (prior.relabel j)) (suc out) Fin.elim0 input tail' step'
  rw [hasRename]
  exact projectionIntro out (rows.relabel j) report

private theorem headFromAccepted (r : Program 3) (rows row tail removed prior : OTerm α)
    (input : D B Γ (consGraph rows row tail))
    (accepted : D B Γ (rowAccept r row removed))
    (tailMap : D B Γ (unary scratchTargets (suc prior) tail)) :
    D B Γ (hasProjection rows) := by
  apply exactOpenInsertedRowCases r B α Γ removed row (hasProjection rows) accepted
  intro β j Δ _ target dom cert keep reported
  have input' := renameInto input j Δ keep
  rw [consGraphRename] at input'
  have tail' := renameInto tailMap j Δ keep
  rw [projectedRename] at tail'
  obtain ⟨decoded⟩ := reported.original
  obtain ⟨envelope⟩ := exactOpenTriple B β Δ 4 (row.relabel j) target dom cert
  have read := Derivation.implicationElimination (Derivation.conjunctionLeft envelope)
    (Derivation.conjunctionLeft decoded)
  rw [hasRename]
  exact finishHead (rows.relabel j) (row.relabel j) (tail.relabel j) target (prior.relabel j)
    input' ⟨Derivation.conjunctionLeft read⟩ reported.targetField tail'

/-- The actual accepted original row and original tail loop supply the
same head fields and a genuine positive prior map. The actual target
step therefore constructs an existential positive map at this cons. -/
theorem exact_AcceptedScanProjectCons (r : Program 3)
    (rows row tail removed : OTerm α)
    (input : D B Γ (consGraph rows row tail))
    (old : D B Γ (loopAccept r rows removed))
    (inherited : D B Γ (atRows r tail removed)) :
    D B Γ (hasProjection rows) := by
  obtain ⟨both⟩ := exactOpenScanCons r B α Γ rows row tail removed input old
  obtain ⟨inherited⟩ := inherited
  have positiveTail : D B Γ (hasProjection tail) :=
    ⟨Derivation.implicationElimination inherited (Derivation.conjunctionRight both)⟩
  have accepted : D B Γ (rowAccept r row removed) := ⟨Derivation.conjunctionLeft both⟩
  apply projectionCases tail (hasProjection rows) positiveTail
  intro β j Δ prior keep tailPos
  have input' := renameInto input j Δ keep
  rw [consGraphRename] at input'
  have accepted' := renameInto accepted j Δ keep
  simp only [rowAccept,programRename,binaryInputsRename,oneTerm,
    NumberedWindowInternalDirectInsertedRowTargets.Zero,sucRelabel,zRelabel] at accepted'
  rw [hasRename]
  exact headFromAccepted r (rows.relabel j) (row.relabel j) (tail.relabel j) (removed.relabel j)
    prior input' accepted' tailPos

#print axioms exact_AcceptedScanProjectCons

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapAcceptedConsProof
