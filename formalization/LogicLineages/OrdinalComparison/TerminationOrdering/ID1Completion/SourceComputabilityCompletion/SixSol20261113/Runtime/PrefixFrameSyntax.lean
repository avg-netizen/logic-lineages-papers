module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PrefixFrameDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem geometrySubst {beta : Type} (agendaPrefix produced suffix old work input joined output : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (geometry agendaPrefix produced suffix old work input joined output).subst (fun a => emb (ts a)) =
 geometry (agendaPrefix.subst ts) (produced.subst ts) (suffix.subst ts) (old.subst ts)
  (work.subst ts) (input.subst ts) (joined.subst ts) (output.subst ts) := by
 simp only [geometry,conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem geometryRename {beta : Type} (agendaPrefix produced suffix old work input joined output : OTerm alpha)
 (j : alpha → beta) :
 (geometry agendaPrefix produced suffix old work input joined output).relabel j =
 geometry (agendaPrefix.relabel j) (produced.relabel j) (suffix.relabel j) (old.relabel j)
  (work.relabel j) (input.relabel j) (joined.relabel j) (output.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (geometry agendaPrefix produced suffix old work input joined output).subst (fun a => emb (.var (j a))) = _
 rw [geometrySubst]
 simp only [← termRelabelAsSubst]
theorem frameSubst {beta : Type} (R : Program 2) (agendaPrefix count produced : OTerm alpha)
 (ts : alpha → OTerm beta) :
 (PrefixFrame R agendaPrefix count produced).subst (fun a => emb (ts a)) =
 PrefixFrame R (agendaPrefix.subst ts) (count.subst ts) (produced.subst ts) := by
 unfold PrefixFrame frameBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [geometrySubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem frameRename {beta : Type} (R : Program 2) (agendaPrefix count produced : OTerm alpha)
 (j : alpha → beta) :
 (PrefixFrame R agendaPrefix count produced).relabel j =
 PrefixFrame R (agendaPrefix.relabel j) (count.relabel j) (produced.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (PrefixFrame R agendaPrefix count produced).subst (fun a => emb (.var (j a))) = _
 rw [frameSubst]
 simp only [← termRelabelAsSubst]
theorem bodyWitness (R : Program 2) (agendaPrefix count produced suffix old work input joined output : OTerm alpha) :
 (frameBody R agendaPrefix count produced).subst (Sum.elim Term.var (fun i => emb (![suffix,old,work,input,joined,output] i))) =
 (geometry agendaPrefix produced suffix old work input joined output).imp
  (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input) := by
 have he : (Sum.elim Term.var (fun i => emb (![suffix,old,work,input,joined,output] i))) =
   (fun a => emb (Sum.elim Term.var ![suffix,old,work,input,joined,output] a)) := by
   funext a
   cases a <;> rfl
 unfold frameBody
 rw [he,impSubst]
 simp only [geometrySubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr,
   Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
   Matrix.head_cons,Matrix.tail_cons]
 rfl
theorem frameApply (R : Program 2) (agendaPrefix count produced suffix old work input joined output : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (PrefixFrame R agendaPrefix count produced)))
 (hg : Nonempty (Derivation body Delta (geometry agendaPrefix produced suffix old work input joined output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input)) := by
 have h := actualFiniteUniversalElimination body alpha 6 Delta (frameBody R agendaPrefix count produced)
   (fun i => emb (![suffix,old,work,input,joined,output] i)) hf
 rw [bodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hg⟩ := hg
 exact ⟨Derivation.implicationElimination h hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
