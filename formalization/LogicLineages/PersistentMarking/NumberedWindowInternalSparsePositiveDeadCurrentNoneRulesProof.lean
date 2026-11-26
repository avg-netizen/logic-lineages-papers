module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneNilProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneRulesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseFieldInductionTargets
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenChecks (exact_OpenNoCurrent)
open NumberedWindowInternalSparsePositiveChosenConsTargets (genuineHead)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph)
open NumberedWindowInternalSparsePositiveDeadCurrentGapChecks (exact_OpenMalformedFinishZero)
open NumberedWindowInternalSparsePositiveDeadCurrentNoneBindingProof
open NumberedWindowInternalSparsePositiveDeadCurrentNoneNilProof (nilZero)

private theorem gapRuleProof (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (gapRule (noneMotive raw least ctx ty))) := by
  let ctx' := ctx.relabel (Sum.inl : α → α ⊕ Fin 1)
  let ty' := ty.relabel (Sum.inl : α → α ⊕ Fin 1)
  let cert : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨d⟩ := exact_OpenMalformedFinishZero body raw least (α ⊕ Fin 1) ctx' ty' z cert
  exact ⟨Derivation.universalIntroduction d⟩

private theorem backToCons {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty cert head tail : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert head tail)))
    (earlier : Nonempty (Derivation body Γ (finishGraph raw least z ctx ty z tail))) :
    Nonempty (Derivation body Γ (finishGraph raw least z ctx ty z cert)) := by
  obtain ⟨out⟩ := exact_OpenNoCurrent body raw least α ctx ty head
  obtain ⟨c⟩ := cell
  have h : Nonempty (Derivation body Γ (genuineHead raw least ctx ty z cert head tail z)) :=
    ⟨Derivation.conjunctionIntroduction c (weakenClosed out Γ)⟩
  obtain ⟨rule⟩ := closedApply (exact_OpenFinishCons body raw least α z ctx ty z cert head tail z) h
  obtain ⟨e⟩ := earlier
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight rule) e⟩

private theorem consRuleProof (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (consRule (noneMotive raw least ctx ty))) := by
  unfold consRule
  apply actualFiniteUniversalIntroduction body α 3 [] (consBody (noneMotive raw least ctx ty))
  unfold consBody
  rw [noneIndex,noneIndex]
  let c := ctx.relabel (Sum.inl : α → α ⊕ Fin 3)
  let t := ty.relabel (Sum.inl : α → α ⊕ Fin 3)
  let cert : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let p := consGraph cert head tail
  let q := finishGraph raw least z c t z tail
  have cell : Derivation body [q,p] p := Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d⟩ := backToCons (Γ := [q,p]) raw least c t cert head tail
    ⟨cell⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem inductionPremises (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    {α : Type} (ctx ty : OTerm α) :
    Nonempty (Derivation body [] (premises (noneMotive raw least ctx ty))) := by
  obtain ⟨nil⟩ := nilZero (body := body) (Γ := []) raw least ctx ty
  obtain ⟨bad⟩ := gapRuleProof body raw least ctx ty
  obtain ⟨good⟩ := consRuleProof body raw least ctx ty
  have base : Derivation body [] (atCode (noneMotive raw least ctx ty) z) :=
    (noneAt raw least ctx ty z).symm ▸ nil
  exact ⟨Derivation.conjunctionIntroduction base (Derivation.conjunctionIntroduction bad good)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentNoneRulesProof
