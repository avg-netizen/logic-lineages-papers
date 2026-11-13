module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
open Runtime.JobFrameSyntax (frameSubst)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem sameSubst {beta : Type} (R : Program 2) (left right parameter : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (SameEvaluator R left right parameter).subst (fun a => emb (ts a)) =
 SameEvaluator R (left.subst ts) (right.subst ts) (parameter.subst ts) := by
 unfold SameEvaluator
 rw [InternalFiniteBlocksSubstitutionProof.existsSubst,liftedEmbedding]
 unfold sameMatrix
 simp only [conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem sameRename {beta : Type} (R : Program 2) (left right parameter : OTerm alpha) (j : alpha → beta) :
 (SameEvaluator R left right parameter).relabel j =
 SameEvaluator R (left.relabel j) (right.relabel j) (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (SameEvaluator R left right parameter).subst (fun a => emb (.var (j a))) = _
 rw [sameSubst]
 simp only [← termRelabelAsSubst]
theorem admittedSubst {beta : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter : OTerm alpha) (ts : alpha → OTerm beta) :
 (AdmittedPair R H G M W left right parameter).subst (fun a => emb (ts a)) =
 AdmittedPair R H G M W (left.subst ts) (right.subst ts) (parameter.subst ts) := by
 simp only [AdmittedPair,conjunctionSubst,graph2,programSubst,numeralSubst,consTermSubst,emptySubst,sameSubst]
theorem admittedRename {beta : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter : OTerm alpha) (j : alpha → beta) :
 (AdmittedPair R H G M W left right parameter).relabel j =
 AdmittedPair R H G M W (left.relabel j) (right.relabel j) (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AdmittedPair R H G M W left right parameter).subst (fun a => emb (.var (j a))) = _
 rw [admittedSubst]
 simp only [← termRelabelAsSubst]
theorem sameInstantiate (R : Program 2) (left right parameter value : OTerm alpha) :
 instantiate (sameMatrix R left right parameter) (emb value) =
 (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value left parameter ⊓
  graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value right parameter) := by
 rw [instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding]
 unfold sameMatrix
 simp only [conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,
   InternalTagArithmeticSyntaxProof.varBind,InternalTagArithmeticSyntaxProof.liftBind]
theorem sameIntro (R : Program 2) (left right parameter value : OTerm alpha)
 (h : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value left parameter ⊓
    graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value right parameter))) :
 Nonempty (Derivation body Delta (SameEvaluator R left right parameter)) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialIntroduction (emb value)
 rw [sameInstantiate]
 exact h
theorem sameCases (R : Program 2) (left right parameter : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (SameEvaluator R left right parameter)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (value : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta
     (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value (left.relabel j) (parameter.relabel j) ⊓
      graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value (right.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialElimination h
 let Theta := sameMatrix R left right parameter :: Delta.map weaken
 exact Classical.choice (next (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
