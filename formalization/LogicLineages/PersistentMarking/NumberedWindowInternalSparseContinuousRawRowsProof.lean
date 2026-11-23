module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawRowsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCertified)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparseAddressSingletonNilProof (finishNil)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- One actual original tape cell. The same checked raw hop and class
transition are owned by the physical head, not independent graphs. -/
structure Row (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (raw : Program 5) (least : Program 3) (ctx ty src q cert tail dst r : OTerm α) : Prop where
  witnesses : ∃ head w : OTerm α,
    Nonempty (Derivation body Γ (consGraph cert head tail)) ∧
    Nonempty (Derivation body Γ (selectedGraph raw least (suc dst) ctx ty (suc src) head)) ∧
    Nonempty (Derivation body Γ (hopCertified head dst q w r))

/-- Nonempty finite directed source tape with *literal raw continuity*.
The cert parameter is the original cons tape; no assembled positive or
application result is an input. Distinct raw class representatives do not
satisfy the same joining index unless related separately. -/
inductive Rows (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (raw : Program 5) (least : Program 3) (ctx ty : OTerm α) :
    OTerm α → OTerm α → OTerm α → OTerm α → OTerm α → Prop where
  | last {src q cert dst r : OTerm α} :
      Row body Γ raw least ctx ty src q cert z dst r →
      Rows body Γ raw least ctx ty src q cert dst r
  | cons {src q cert tail mid r dst t : OTerm α} :
      Row body Γ raw least ctx ty src q cert tail mid r →
      Rows body Γ raw least ctx ty mid r tail dst t →
      Rows body Γ raw least ctx ty src q cert dst t

private theorem finishCons (raw : Program 5) (least : Program 3)
    (ctx ty src cert tail mid dst head : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert head tail)))
    (advance : Nonempty (Derivation body Γ (selectedGraph raw least (suc mid) ctx ty (suc src) head)))
    (finish : Nonempty (Derivation body Γ (finishAt raw least ctx ty mid tail dst))) :
    Nonempty (Derivation body Γ (finishAt raw least ctx ty src cert dst)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := advance
  obtain ⟨f⟩ := finish
  obtain ⟨pair⟩ := closedApply (exact_OpenFinishCons body raw least α (suc dst)
    ctx ty (suc src) cert head tail (suc mid)) ⟨Derivation.conjunctionIntroduction c a⟩
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight pair) f⟩

theorem Rows.toFinish {raw : Program 5} {least : Program 3} {ctx ty src q cert dst r : OTerm α}
    (known : Rows body Γ raw least ctx ty src q cert dst r) :
    Nonempty (Derivation body Γ (finishAt raw least ctx ty src cert dst)) := by
  induction known with
  | @last source _ cert target _ row =>
    obtain ⟨head,_,hc,advance,_⟩ := row.witnesses
    exact finishCons raw least ctx ty source cert z target target head hc advance
      (finishNil raw least ctx ty target)
  | @cons source _ cert tail mid _ target _ row _ ih =>
    obtain ⟨head,_,hc,advance,_⟩ := row.witnesses
    exact finishCons raw least ctx ty source cert tail mid target head hc advance ih

#print axioms Rows.toFinish
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseContinuousRawRowsProof
