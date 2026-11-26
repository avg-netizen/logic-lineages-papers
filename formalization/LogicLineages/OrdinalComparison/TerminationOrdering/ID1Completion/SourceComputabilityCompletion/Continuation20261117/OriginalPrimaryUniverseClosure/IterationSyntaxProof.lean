module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationSyntaxProof
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
    (count pool reached parameter gamma context : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
    (AtCount n arity count pool reached parameter gamma context).subst (fun a => emb (ts a)) =
      AtCount n arity (count.subst ts) (pool.subst ts) (reached.subst ts)
        (parameter.subst ts) (gamma.subst ts) (context.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,allAcceptedSubst,graph4,programSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atCountRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter gamma context : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (AtCount n arity count pool reached parameter gamma context).relabel j =
      AtCount n arity (count.relabel j) (pool.relabel j) (reached.relabel j)
        (parameter.relabel j) (gamma.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount n arity count pool reached parameter gamma context).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (count pool reached parameter gamma context out : OrdinaryArithmetic.Term alpha) :
    (matrix n arity count pool reached parameter gamma context).subst
      (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
      (graph4 (PrimaryIteration.iterate (OriginalConcreteStructuralEdge.edge n arity))
        out count pool reached parameter).imp
        ((allAccepted n arity reached gamma context).imp (allAccepted n arity out gamma context)) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb out)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => out) a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,allAcceptedSubst,graph4,programSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.IterationSyntaxProof
