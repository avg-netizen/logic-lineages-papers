module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawRowsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawRowsPositiveProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCertified)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt headData)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveHeadDecompositionChecks (exact_OpenPositiveHeadDecomposition)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (provideHead)
open NumberedWindowInternalSparseAddressSingletonNilProof (finishNil)

open NumberedWindowInternalSparseContinuousRawRowsProof (Rows)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem positiveCons (raw : Program 5) (least : Program 3)
    (ctx ty src cert tail mid dst head : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert head tail)))
    (advance : Nonempty (Derivation body Γ (selectedGraph raw least (suc mid) ctx ty (suc src) head)))
    (finish : Nonempty (Derivation body Γ (finishAt raw least ctx ty mid tail dst))) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty src cert dst)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := advance
  obtain ⟨f⟩ := finish
  have data : Nonempty (Derivation body Γ (headData raw least ctx ty src cert dst head tail mid)) :=
    ⟨Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction a f)⟩
  obtain ⟨provided⟩ := provideHead raw least ctx ty src cert dst head tail mid data
  obtain ⟨eqv⟩ := exact_OpenPositiveHeadDecomposition body raw least α ctx ty src cert dst
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight (weakenClosed eqv Γ)) provided⟩

attribute [local irreducible] positiveAt finishAt

private theorem headWitness {raw : Program 5} {least : Program 3} {ctx ty src q cert dst r : OTerm α}
    (known : Rows body Γ raw least ctx ty src q cert dst r) :
    ∃ head tail mid : OTerm α,
      Nonempty (Derivation body Γ (consGraph cert head tail)) ∧
      Nonempty (Derivation body Γ (selectedGraph raw least (suc mid) ctx ty (suc src) head)) ∧
      Nonempty (Derivation body Γ (finishAt raw least ctx ty mid tail dst)) := by
  induction known with
  | @last source left code target right row =>
    obtain ⟨head,witness,cell,advance,owned⟩ := row.witnesses
    exact ⟨head,z,target,cell,advance,finishNil raw least ctx ty target⟩
  | @cons source left code tail mid joinRaw target right row rest _ =>
    obtain ⟨head,witness,cell,advance,owned⟩ := row.witnesses
    exact ⟨head,tail,mid,cell,advance,
      Rows.toFinish (body := body) (Γ := Γ) (raw := raw) (least := least)
        (ctx := ctx) (ty := ty) (src := mid) (q := joinRaw) (cert := tail)
        (dst := target) (r := right) rest⟩

/-- The held finite directed tape actually produces its own original
nonempty certificate acceptance. Path acceptance was not a premise. -/
theorem toPositive {raw : Program 5} {least : Program 3} {ctx ty src q cert dst r : OTerm α}
    (known : Rows body Γ raw least ctx ty src q cert dst r) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty src cert dst)) := by
  obtain ⟨head,tail,mid,cell,advance,done⟩ := headWitness known
  exact positiveCons raw least ctx ty src cert tail mid dst head cell advance done

#print axioms toPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawRowsPositiveProof
