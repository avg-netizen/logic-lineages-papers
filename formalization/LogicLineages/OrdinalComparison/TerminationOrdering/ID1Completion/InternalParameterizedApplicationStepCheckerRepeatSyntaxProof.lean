module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker InternalRawListRecursionSyntaxProof InternalListCodec
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalListInduction InternalListInductionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem repeatRename {α β : Type} (transition : Program 2)
    (out code initial parameter : OTerm α) (j : α → β) :
    (repeatGraph transition out code initial parameter).relabel j =
      repeatGraph transition (out.relabel j) (code.relabel j) (initial.relabel j) (parameter.relabel j) := by
  simp only [repeatGraph,graph3Rename]

@[simp] theorem repeatSubst {α β : Type} (transition : Program 2)
    (out code initial parameter : OTerm α) (ts : α → OTerm β) :
    (repeatGraph transition out code initial parameter).subst (fun a => emb (ts a)) =
      repeatGraph transition (out.subst ts) (code.subst ts) (initial.subst ts) (parameter.subst ts) := by
  simp only [repeatGraph,graph3,programSubst,consTermSubst,emptySubst]

/-- The original four state variables and the unchanged parameter are all
quantified inside the list-induction invariant. No parameter is encoded in
the raw list or transition state. -/
def commuteBody {α : Type} (transition : Program 2) (code : OTerm α) :
    Formula (α ⊕ Fin 5) :=
  (graph2 transition (.var (.inr 1)) (.var (.inr 0)) (.var (.inr 4)) ⊓
    (repeatGraph transition (.var (.inr 2)) (code.relabel Sum.inl)
        (.var (.inr 0)) (.var (.inr 4)) ⊓
      graph2 transition (.var (.inr 3)) (.var (.inr 2)) (.var (.inr 4)))).imp
    (repeatGraph transition (.var (.inr 3)) (code.relabel Sum.inl)
      (.var (.inr 1)) (.var (.inr 4)))

def commuteRow {α : Type} (transition : Program 2) (code : OTerm α) : Formula α :=
  allBlock (commuteBody transition code)

theorem commuteRowSubst {α β : Type} (transition : Program 2)
    (code : OTerm α) (ts : α → OTerm β) :
    (commuteRow transition code).subst (fun a => emb (ts a)) =
      commuteRow transition (code.subst ts) := by
  unfold commuteRow commuteBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2,programSubst,repeatSubst,consTermSubst,liftSubst,
    Term.subst,Sum.elim_inr,emptySubst]

theorem commuteRowRename {α β : Type} (transition : Program 2)
    (code : OTerm α) (j : α → β) :
    (commuteRow transition code).relabel j = commuteRow transition (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (commuteRow transition code).subst (fun a => emb (.var (j a))) = _
  rw [commuteRowSubst]
  simp only [← termRelabelAsSubst]

theorem commuteBodyWitness {α : Type} (transition : Program 2)
    (code initial next result out parameter : OTerm α) :
    (commuteBody transition code).subst
      (Sum.elim Term.var (fun i => emb (![initial,next,result,out,parameter] i))) =
      (graph2 transition next initial parameter ⊓
        (repeatGraph transition result code initial parameter ⊓
          graph2 transition out result parameter)).imp
        (repeatGraph transition out code next parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![initial,next,result,out,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![initial,next,result,out,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold commuteBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2,programSubst,repeatSubst,consTermSubst,witnessLift,
    Term.subst,Sum.elim_inr,emptySubst]
  rfl

theorem commuteAtCode {α : Type} (transition : Program 2) (code : OTerm α) :
    atCode (commuteRow transition (.var (.inr (0 : Fin 1)))) code =
      commuteRow transition code := by
  simp only [atCode,instantiate,bindEmbedding,commuteRowSubst,varBind]

theorem commuteAtIndex {α : Type} (transition : Program 2) (i : Fin 3) :
    atIndex (commuteRow transition (.var (.inr (0 : Fin 1))) : Formula (α ⊕ Fin 1)) i =
      commuteRow transition (.var (.inr i)) := by
  rw [atIndex,commuteRowRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
