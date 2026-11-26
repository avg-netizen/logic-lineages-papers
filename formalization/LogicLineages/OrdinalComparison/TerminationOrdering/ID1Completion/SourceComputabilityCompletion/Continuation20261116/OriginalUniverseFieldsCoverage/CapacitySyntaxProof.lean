module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ScalarSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacitySyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction
variable {alpha : Type}
attribute [local irreducible] programGraph
open ScalarSyntaxProof

theorem capacitySubst {beta : Type} (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ts : alpha → OTerm beta) :
    (capacity n raw xs).subst (fun a => emb (ts a)) =
      capacity n (raw.subst ts) (fun i => (xs i).subst ts) := by
  unfold capacity capacityBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,InternalLessThan.strictLess,orderSubst,sucSubst,
    fieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem capacityRename {beta : Type} (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (j : alpha → beta) :
    (capacity n raw xs).relabel j = capacity n (raw.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (capacity n raw xs).subst (fun a => emb (.var (j a))) = _
  rw [capacitySubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacitySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacitySyntaxProof
