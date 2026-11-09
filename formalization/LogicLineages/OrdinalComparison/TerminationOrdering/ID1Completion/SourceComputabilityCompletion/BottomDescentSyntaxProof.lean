module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.BottomRepresentative SourceComputabilityCompletion.BottomDescent
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalParameterizedBoundedDescentNormalizerSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof InternalRawListRecursionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem rowSubst {α β : Type} (data : Data) (window : Program 1)
    (count : OTerm α) (ts : α → OTerm β) :
    (iterationRow data window count).subst (fun a => emb (ts a)) =
      iterationRow data window (count.subst ts) := by
  unfold BottomDescent.iterationRow BottomDescent.iterationBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [conjunctionSubst,repeatSubst,activeSubst,bottomSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {α β : Type} (data : Data) (window : Program 1)
    (count : OTerm α) (j : α → β) :
    (iterationRow data window count).relabel j = iterationRow data window (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (iterationRow data window count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem bodyWitness {α : Type} (data : Data) (window : Program 1)
    (count input out parameter indicator : OTerm α) :
    (iterationBody data window count).subst
      (Sum.elim Term.var (fun i => emb (![input,out,parameter,indicator] i))) =
      (InternalParameterizedNumericIteration.repeatGraph (step data window) out count input parameter ⊓
        (activeGraph data window input parameter ⊓ bottomGraph indicator input)).imp
        (bottomGraph indicator out) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,out,parameter,indicator] i))) =
      (fun a => emb (Sum.elim Term.var ![input,out,parameter,indicator] a)) := by
    funext a
    cases a <;> rfl
  unfold BottomDescent.iterationBody
  rw [he,impSubst]
  simp only [conjunctionSubst,repeatSubst,activeSubst,bottomSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate {α : Type} (data : Data) (window : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (iterationRow data window count) (emb t) =
      iterationRow data window (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor {α : Type} (data : Data) (window : Program 1)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (iterationRow data window count) =
      iterationRow data window (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentSyntaxProof
