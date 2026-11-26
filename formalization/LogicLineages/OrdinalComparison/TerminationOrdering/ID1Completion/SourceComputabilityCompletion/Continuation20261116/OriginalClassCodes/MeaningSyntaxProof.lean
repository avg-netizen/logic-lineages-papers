module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericObservationsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst eqnSubst)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Meaning
attribute [local irreducible] programGraph

theorem frozenBlock {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) :
    Targets.meaning n arity H seed param candidate = InternalFiniteBlocks.block (matrix n arity H seed param candidate) := rfl

theorem observationsSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha) (ts : alpha → OTerm beta) :
    (observations n arity H seed param candidate xs).subst (fun a => emb (ts a)) =
      observations n arity H (seed.subst ts) (param.subst ts) (candidate.subst ts) (fun i => (xs i).subst ts) := by
  apply GenericObservationsSyntaxProof.subst
    ![rootType,types,heads n arity,size n,labels n,bound,fuel n,admitted n H]
    InternalPairing.pairing seed param candidate xs ts
  · exact OriginalEnumerationMembership.SixArgumentSubstitutionProof.acceptedSubst
      (OriginalEnumerationFields.fields n) (xs 0) (xs 6) (xs 2) (xs 3) (xs 5) (xs 4) ts
  · exact OriginalEnumerationMembership.DepthSyntaxProof.boundSubst n (xs 0) (xs 7) ts


theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha) :
    (matrix n arity H seed param candidate).subst (Sum.elim Term.var (fun i => emb (xs i))) =
      observations n arity H seed param candidate xs := by
  have he : (Sum.elim Term.var (fun i => emb (xs i))) =
      (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,observationsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningSyntaxProof
