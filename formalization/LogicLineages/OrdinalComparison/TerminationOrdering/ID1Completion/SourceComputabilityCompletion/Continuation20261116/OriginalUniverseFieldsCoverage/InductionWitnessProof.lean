module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalSourceIntroductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction ScalarSyntaxProof ResultSyntaxProof
variable {alpha : Type}
attribute [local irreducible] programGraph

theorem matrixWitness (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) :
    (matrix n arity H arguments raw).subst (Sum.elim Term.var (fun i => emb (xs i))) =
      (observations n arity H arguments raw xs).imp (result n arguments raw xs) := by
  have he : Sum.elim Term.var (fun i => emb (xs i)) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,InternalAdditionLawsProof.impSubst,observationsSubst,resultSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionWitnessProof
