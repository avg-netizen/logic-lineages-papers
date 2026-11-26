module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalSourceIntroductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction SyntaxProof
variable {alpha : Type}
attribute [local irreducible] programGraph

theorem matrixWitness (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 6 → OTerm alpha) :
    (matrix n H arguments raw).subst (Sum.elim Term.var (fun i => emb (xs i))) =
      (observations n H arguments raw xs).imp (result arguments (xs 3) (xs 5)) := by
  have he : Sum.elim Term.var (fun i => emb (xs i)) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,InternalAdditionLawsProof.impSubst,observationsSubst,resultSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionWitnessProof
