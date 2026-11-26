module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerFixedSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalListInduction InternalListInductionSyntaxProof InternalRawListRecursionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Initial state and parameter are universally bound INSIDE the original
list-code induction invariant. The code is not numerical iteration fuel. -/
def fixedBody {α : Type} (transition : Program 2) (code : OTerm α) :
    Formula (α ⊕ Fin 2) :=
  (graph2 transition (.var (.inr 0)) (.var (.inr 0)) (.var (.inr 1))).imp
    (repeatGraph transition (.var (.inr 0)) (code.relabel Sum.inl)
      (.var (.inr 0)) (.var (.inr 1)))

def fixedRow {α : Type} (transition : Program 2) (code : OTerm α) : Formula α :=
  allBlock (fixedBody transition code)

theorem fixedRowSubst {α β : Type} (transition : Program 2)
    (code : OTerm α) (ts : α → OTerm β) :
    (fixedRow transition code).subst (fun a => emb (ts a)) =
      fixedRow transition (code.subst ts) := by
  unfold fixedRow fixedBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [graph2,programSubst,repeatSubst,consTermSubst,liftSubst,
    Term.subst,Sum.elim_inr,emptySubst]

theorem fixedRowRename {α β : Type} (transition : Program 2)
    (code : OTerm α) (j : α → β) :
    (fixedRow transition code).relabel j = fixedRow transition (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fixedRow transition code).subst (fun a => emb (.var (j a))) = _
  rw [fixedRowSubst]
  simp only [← termRelabelAsSubst]

theorem fixedBodyWitness {α : Type} (transition : Program 2)
    (code initial parameter : OTerm α) :
    (fixedBody transition code).subst
      (Sum.elim Term.var (fun i => emb (![initial,parameter] i))) =
      (graph2 transition initial initial parameter).imp
        (repeatGraph transition initial code initial parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![initial,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![initial,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold fixedBody
  rw [he,impSubst]
  simp only [graph2,programSubst,repeatSubst,consTermSubst,witnessLift,
    Term.subst,Sum.elim_inr,emptySubst]
  rfl

theorem fixedAtCode {α : Type} (transition : Program 2) (code : OTerm α) :
    atCode (fixedRow transition (.var (.inr (0 : Fin 1)))) code =
      fixedRow transition code := by
  simp only [atCode,instantiate,bindEmbedding,fixedRowSubst,varBind]

theorem fixedAtIndex {α : Type} (transition : Program 2) (i : Fin 3) :
    atIndex (fixedRow transition (.var (.inr (0 : Fin 1))) : Formula (α ⊕ Fin 1)) i =
      fixedRow transition (.var (.inr i)) := by
  rw [atIndex,fixedRowRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerFixedSyntaxProof
