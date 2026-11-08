module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalRawListRecursionSyntaxProof InternalListCodec
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalListInduction InternalListInductionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem repeatRename {α β : Type} (transition : Program 1)
    (out code initial : OTerm α) (j : α → β) :
    (repeatGraph transition out code initial).relabel j =
      repeatGraph transition (out.relabel j) (code.relabel j) (initial.relabel j) := by
  simp only [repeatGraph,programRename,consTermRename,emptyRename]

@[simp] theorem repeatSubst {α β : Type} (transition : Program 1)
    (out code initial : OTerm α) (ts : α → OTerm β) :
    (repeatGraph transition out code initial).subst (fun a => emb (ts a)) =
      repeatGraph transition (out.subst ts) (code.subst ts) (initial.subst ts) := by
  simp only [repeatGraph,programSubst,consTermSubst,emptySubst]

/-- Four universally quantified states make commutation available at the
intermediate tail result, not merely at one chosen initial state. -/
def commuteBody {α : Type} (transition : Program 1) (code : OTerm α) :
    Formula (α ⊕ Fin 4) :=
  (programGraph transition (.var (.inr 1)) (Fin.cons (.var (.inr 0)) Fin.elim0) ⊓
    (repeatGraph transition (.var (.inr 2)) (code.relabel Sum.inl) (.var (.inr 0)) ⊓
      programGraph transition (.var (.inr 3)) (Fin.cons (.var (.inr 2)) Fin.elim0))).imp
    (repeatGraph transition (.var (.inr 3)) (code.relabel Sum.inl) (.var (.inr 1)))

def commuteRow {α : Type} (transition : Program 1) (code : OTerm α) : Formula α :=
  allBlock (commuteBody transition code)

theorem commuteRowSubst {α β : Type} (transition : Program 1)
    (code : OTerm α) (ts : α → OTerm β) :
    (commuteRow transition code).subst (fun a => emb (ts a)) =
      commuteRow transition (code.subst ts) := by
  unfold commuteRow commuteBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [programSubst,repeatSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem commuteRowRename {α β : Type} (transition : Program 1)
    (code : OTerm α) (j : α → β) :
    (commuteRow transition code).relabel j = commuteRow transition (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (commuteRow transition code).subst (fun a => emb (.var (j a))) = _
  rw [commuteRowSubst]
  simp only [← termRelabelAsSubst]

theorem commuteBodyWitness {α : Type} (transition : Program 1)
    (code initial next result out : OTerm α) :
    (commuteBody transition code).subst
      (Sum.elim Term.var (fun i => emb (![initial,next,result,out] i))) =
      (programGraph transition next (Fin.cons initial Fin.elim0) ⊓
        (repeatGraph transition result code initial ⊓
          programGraph transition out (Fin.cons result Fin.elim0))).imp
        (repeatGraph transition out code next) := by
  have he : (Sum.elim Term.var (fun i => emb (![initial,next,result,out] i))) =
      (fun a => emb (Sum.elim Term.var ![initial,next,result,out] a)) := by
    funext a
    cases a <;> rfl
  unfold commuteBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [programSubst,repeatSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst]
  rfl

theorem commuteInstantiate {α : Type} (transition : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (commuteRow transition count) (emb t) =
      commuteRow transition (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,commuteRowSubst]

theorem commuteSuccessor {α : Type} (transition : Program 1)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (commuteRow transition count) =
      commuteRow transition (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,commuteRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSyntaxProof
