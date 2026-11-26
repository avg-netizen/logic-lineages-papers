module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
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
open UniformReturnDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem geometrySubst {beta : Type} (frame produced value suffix old work results input pushed output : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (geometry frame produced value suffix old work results input pushed output).subst (fun a => emb (ts a)) =
 geometry (frame.subst ts) (produced.subst ts) (value.subst ts) (suffix.subst ts) (old.subst ts)
  (work.subst ts) (results.subst ts) (input.subst ts) (pushed.subst ts) (output.subst ts) := by
 simp only [geometry,numeralSubst,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem geometryRename {beta : Type} (frame produced value suffix old work results input pushed output : OTerm alpha)
 (j : alpha → beta) :
 (geometry frame produced value suffix old work results input pushed output).relabel j =
 geometry (frame.relabel j) (produced.relabel j) (value.relabel j) (suffix.relabel j) (old.relabel j)
  (work.relabel j) (results.relabel j) (input.relabel j) (pushed.relabel j) (output.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (geometry frame produced value suffix old work results input pushed output).subst (fun a => emb (.var (j a))) = _
 rw [geometrySubst]
 simp only [← termRelabelAsSubst]
theorem frameSubst {beta : Type} (R : Program 2) (frame produced value : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (Framed R frame produced value).subst (fun a => emb (ts a)) =
 Framed R (frame.subst ts) (produced.subst ts) (value.subst ts) := by
 unfold Framed frameBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [geometrySubst,InternalTagArithmeticSyntaxProof.sucSubst,numeralSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem frameRename {beta : Type} (R : Program 2) (frame produced value : OTerm alpha)
 (j : alpha → beta) :
 (Framed R frame produced value).relabel j =
 Framed R (frame.relabel j) (produced.relabel j) (value.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Framed R frame produced value).subst (fun a => emb (.var (j a))) = _
 rw [frameSubst]
 simp only [← termRelabelAsSubst]
theorem bodyWitness (R : Program 2) (frame produced value suffix old work results input pushed output : OTerm alpha) :
 (frameBody R frame produced value).subst (Sum.elim Term.var (fun i => emb (![suffix,old,work,results,input,pushed,output] i))) =
 (geometry frame produced value suffix old work results input pushed output).imp
  (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (InternalTagArithmeticSyntaxProof.suc (numeral 0)) input) := by
 have he : (Sum.elim Term.var (fun i => emb (![suffix,old,work,results,input,pushed,output] i))) =
   (fun a => emb (Sum.elim Term.var ![suffix,old,work,results,input,pushed,output] a)) := by
   funext a
   cases a <;> rfl
 unfold frameBody
 rw [he,impSubst]
 simp only [geometrySubst,InternalTagArithmeticSyntaxProof.sucSubst,numeralSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
   Matrix.head_cons,Matrix.tail_cons]
 rfl
theorem frameApply (R : Program 2) (frame produced value suffix old work results input pushed output : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Framed R frame produced value)))
 (hg : Nonempty (Derivation body Delta (geometry frame produced value suffix old work results input pushed output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (InternalTagArithmeticSyntaxProof.suc (numeral 0)) input)) := by
 have h := actualFiniteUniversalElimination body alpha 7 Delta (frameBody R frame produced value)
   (fun i => emb (![suffix,old,work,results,input,pushed,output] i)) hf
 rw [bodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hg⟩ := hg
 exact ⟨Derivation.implicationElimination h hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
