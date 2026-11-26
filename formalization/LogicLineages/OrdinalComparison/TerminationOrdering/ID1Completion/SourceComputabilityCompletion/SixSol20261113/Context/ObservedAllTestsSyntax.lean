module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalClassContextAllPositionObserver OriginalContextInsertion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ObservedAllTestsDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem boundedSubst {beta : Type} (R : Program 2) (count seed candidate parameter : InternalGraphComposition.OTerm alpha)
 (ts : alpha → InternalGraphComposition.OTerm beta) :
 (BoundedTests R count seed candidate parameter).subst (fun a => emb (ts a)) =
 BoundedTests R (count.subst ts) (seed.subst ts) (candidate.subst ts) (parameter.subst ts) := by
 unfold BoundedTests boundedMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [Below,orderSubst,graph4,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr,sucSubst,zSubst]
theorem boundedRename {beta : Type} (R : Program 2) (count seed candidate parameter : InternalGraphComposition.OTerm alpha)
 (j : alpha → beta) :
 (BoundedTests R count seed candidate parameter).relabel j =
 BoundedTests R (count.relabel j) (seed.relabel j) (candidate.relabel j) (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (BoundedTests R count seed candidate parameter).subst (fun a => emb (.var (j a))) = _
 rw [boundedSubst]
 simp only [← termRelabelAsSubst]
theorem boundedWitness (R : Program 2) (count seed candidate parameter cutoff : InternalGraphComposition.OTerm alpha) :
 (boundedMatrix R count seed candidate parameter).subst (Sum.elim Term.var (fun _ : Fin 1 => emb cutoff)) =
 (Below cutoff count).imp (graph4 (positionTest R) (suc z) cutoff seed candidate parameter) := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb cutoff)) =
   (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => cutoff) a)) := by funext a; cases a <;> rfl
 unfold boundedMatrix
 rw [he,impSubst]
 simp only [Below,orderSubst,graph4,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr,sucSubst,zSubst]
theorem boundedApply (R : Program 2) (count seed candidate parameter cutoff : InternalGraphComposition.OTerm alpha)
 (h : Nonempty (Derivation body Delta (BoundedTests R count seed candidate parameter)))
 (hb : Nonempty (Derivation body Delta (Below cutoff count))) :
 Nonempty (Derivation body Delta (graph4 (positionTest R) (suc z) cutoff seed candidate parameter)) := by
 have h := actualFiniteUniversalElimination body alpha 1 Delta
   (boundedMatrix R count seed candidate parameter) (fun _ => emb cutoff) h
 rw [boundedWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.implicationElimination h hb⟩
def row (R : Program 2) (count seed candidate parameter : InternalGraphComposition.OTerm alpha) : Formula alpha :=
 (BoundedTests R count seed candidate parameter).imp
 (graph4 (scan R) (suc z) count seed candidate parameter)
theorem rowSubst {beta : Type} (R : Program 2) (count seed candidate parameter : InternalGraphComposition.OTerm alpha)
 (ts : alpha → InternalGraphComposition.OTerm beta) :
 (row R count seed candidate parameter).subst (fun a => emb (ts a)) =
 row R (count.subst ts) (seed.subst ts) (candidate.subst ts) (parameter.subst ts) := by
 simp only [row,impSubst,boundedSubst,graph4,programSubst,consTermSubst,emptySubst,sucSubst,zSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsSyntax
