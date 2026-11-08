module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalNumericIterationSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Quantify the first count and every state INSIDE the induction row for
its second count. This is a genuine full-language invariant. -/
def fusionBody {α : Type} (transition : Program 1) (count : OTerm α) :
    Formula (α ⊕ Fin 4) :=
  (repeatGraph transition (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1)) ⊓
    repeatGraph transition (.var (.inr 3)) (count.relabel Sum.inl) (.var (.inr 2))).imp
    (repeatGraph transition (.var (.inr 3))
      (OrdinaryArithmetic.addTerm (.var (.inr 0)) (count.relabel Sum.inl)) (.var (.inr 1)))

def fusionRow {α : Type} (transition : Program 1) (count : OTerm α) : Formula α :=
  allBlock (fusionBody transition count)

theorem fusionRowSubst {α β : Type} (transition : Program 1)
    (count : OTerm α) (ts : α → OTerm β) :
    (fusionRow transition count).subst (fun a => emb (ts a)) =
      fusionRow transition (count.subst ts) := by
  unfold fusionRow fusionBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [repeatSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem fusionRowRename {α β : Type} (transition : Program 1)
    (count : OTerm α) (j : α → β) :
    (fusionRow transition count).relabel j = fusionRow transition (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fusionRow transition count).subst (fun a => emb (.var (j a))) = _
  rw [fusionRowSubst]
  simp only [← termRelabelAsSubst]

theorem fusionBodyWitness {α : Type} (transition : Program 1)
    (count first initial intermediate out : OTerm α) :
    (fusionBody transition count).subst
      (Sum.elim Term.var (fun i => emb (![first,initial,intermediate,out] i))) =
      (repeatGraph transition intermediate first initial ⊓
        repeatGraph transition out count intermediate).imp
        (repeatGraph transition out (OrdinaryArithmetic.addTerm first count) initial) := by
  have he : (Sum.elim Term.var (fun i => emb (![first,initial,intermediate,out] i))) =
      (fun a => emb (Sum.elim Term.var ![first,initial,intermediate,out] a)) := by
    funext a
    cases a <;> rfl
  unfold fusionBody
  rw [he,impSubst,conjunctionSubst]
  simp only [repeatSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem fusionInstantiate {α : Type} (transition : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (fusionRow transition count) (emb t) =
      fusionRow transition (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,fusionRowSubst]

theorem fusionSuccessor {α : Type} (transition : Program 1)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (fusionRow transition count) =
      fusionRow transition (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,fusionRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionSyntaxProof
