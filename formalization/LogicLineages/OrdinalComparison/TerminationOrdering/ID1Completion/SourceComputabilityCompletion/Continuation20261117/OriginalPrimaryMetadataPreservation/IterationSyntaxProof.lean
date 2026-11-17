module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open Iteration SyntaxProof

theorem atCountSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter rootTypeRef boundsRef : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
    (AtCount n arity count pool reached parameter rootTypeRef boundsRef).subst (fun a => emb (ts a)) =
      AtCount n arity (count.subst ts) (pool.subst ts) (reached.subst ts)
        (parameter.subst ts) (rootTypeRef.subst ts) (boundsRef.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,allAcceptedSubst,graph4,programSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atCountRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter rootTypeRef boundsRef : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (AtCount n arity count pool reached parameter rootTypeRef boundsRef).relabel j =
      AtCount n arity (count.relabel j) (pool.relabel j) (reached.relabel j)
        (parameter.relabel j) (rootTypeRef.relabel j) (boundsRef.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount n arity count pool reached parameter rootTypeRef boundsRef).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter rootTypeRef boundsRef out : OrdinaryArithmetic.Term alpha) :
    (matrix n arity count pool reached parameter rootTypeRef boundsRef).subst
      (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
      (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity))
        out count pool reached parameter).imp
        ((allAccepted n arity reached rootTypeRef boundsRef).imp (allAccepted n arity out rootTypeRef boundsRef)) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => out) a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,allAcceptedSubst,graph4,programSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationSyntaxProof
