module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ResultSyntaxProof
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
open ScalarSyntaxProof CapacitySyntaxProof

theorem intrinsicSubst {beta : Type} (n : Nat) (arguments : Bool) (raw : OTerm alpha)
    (xs : Fin 11 → OTerm alpha) (ts : alpha → OTerm beta) :
    (intrinsic n arguments raw xs).subst (fun a => emb (ts a)) =
      intrinsic n arguments (raw.subst ts) (fun i => (xs i).subst ts) := by
  cases arguments <;> simp only [intrinsic,conjunctionSubst,
    OriginalEnumerationFields.Types.AllowedSyntaxProof.allowedSubst,InternalLessThan.strictLess,orderSubst,
    graph1,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,
    numeral,sucSubst,zSubst,Bool.false_eq_true,if_true,if_false]

theorem resultSubst {beta : Type} (n : Nat) (arguments : Bool) (raw : OTerm alpha)
    (xs : Fin 11 → OTerm alpha) (ts : alpha → OTerm beta) :
    (result n arguments raw xs).subst (fun a => emb (ts a)) =
      result n arguments (raw.subst ts) (fun i => (xs i).subst ts) := by
  simp only [result,conjunctionSubst,intrinsicSubst,capacitySubst]

theorem resultRename {beta : Type} (n : Nat) (arguments : Bool) (raw : OTerm alpha)
    (xs : Fin 11 → OTerm alpha) (j : alpha → beta) :
    (result n arguments raw xs).relabel j = result n arguments (raw.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (result n arguments raw xs).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

theorem observationsRename {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) (j : alpha → beta) :
    (observations n arity H arguments raw xs).relabel j =
      observations n arity H arguments (raw.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observations n arity H arguments raw xs).subst (fun a => emb (.var (j a))) = _
  rw [observationsSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ResultSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ResultSyntaxProof
