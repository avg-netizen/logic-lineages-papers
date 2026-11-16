module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningRenameProof
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

open MeaningSyntaxProof
@[simp] theorem observationsRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha) (j : alpha → beta) :
    (observations n arity H seed param candidate xs).relabel j =
      observations n arity H (seed.relabel j) (param.relabel j) (candidate.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observations n arity H seed param candidate xs).subst (fun a => emb (.var (j a))) = _
  rw [observationsSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem meaningRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (j : alpha → beta) :
    (Targets.meaning n arity H seed param candidate).relabel j =
      Targets.meaning n arity H (seed.relabel j) (param.relabel j) (candidate.relabel j) := by
  simp only [frozenBlock,InternalOriginalObjectFiberCertifiedLiftSyntaxProof.blockRename,matrix,
    observationsRename,Term.relabel_relabel,Term.relabel]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningRenameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningRenameProof
