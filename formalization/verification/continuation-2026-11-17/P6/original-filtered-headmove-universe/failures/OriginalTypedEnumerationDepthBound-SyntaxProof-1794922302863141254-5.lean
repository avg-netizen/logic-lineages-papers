module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SyntaxProof
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
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction
variable {alpha : Type}
attribute [local irreducible] programGraph

theorem resultSubst {beta : Type} (arguments : Bool) (size depth : OTerm alpha) (ts : alpha → OTerm beta) :
    (result arguments size depth).subst (fun a => emb (ts a)) = result arguments (size.subst ts) (depth.subst ts) := by
  cases arguments <;> simp only [result,termBound,argumentsBound,twice,InternalLessThan.strictLess,
    conjunctionSubst,orderSubst,sucSubst,addSubst,zSubst,Bool.false_eq_true,if_true,if_false]

theorem acceptedSubst {beta : Type} (H : Program 1) (arguments : Bool) (typ raw gamma : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (accepted H arguments typ raw gamma).subst (fun a => emb (ts a)) =
      accepted H arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) := by
  cases arguments <;> simp only [accepted,termAcceptedSubst,argumentsAcceptedSubst,
    Bool.false_eq_true,if_true,if_false]

theorem observationsSubst {beta : Type} (n : Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 6 → OTerm alpha) (ts : alpha → OTerm beta) :
    (observations n H arguments raw xs).subst (fun a => emb (ts a)) =
      observations n H arguments (raw.subst ts) (fun i => (xs i).subst ts) := by
  simp only [observations,conjunctionSubst,acceptedSubst,graph1,graph2,
    InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,numeral,sucSubst,zSubst]

theorem resultRename {beta : Type} (arguments : Bool) (size depth : OTerm alpha) (j : alpha → beta) :
    (result arguments size depth).relabel j = result arguments (size.relabel j) (depth.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (result arguments size depth).subst (fun a => emb (.var (j a))) = _
  rw [resultSubst]
  simp only [← termRelabelAsSubst]

theorem acceptedRename {beta : Type} (H : Program 1) (arguments : Bool) (typ raw gamma : OTerm alpha)
    (j : alpha → beta) :
    (accepted H arguments typ raw gamma).relabel j =
      accepted H arguments (typ.relabel j) (raw.relabel j) (gamma.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (accepted H arguments typ raw gamma).subst (fun a => emb (.var (j a))) = _
  rw [acceptedSubst]
  simp only [← termRelabelAsSubst]

theorem observationsRename {beta : Type} (n : Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 6 → OTerm alpha) (j : alpha → beta) :
    (observations n H arguments raw xs).relabel j =
      observations n H arguments (raw.relabel j) (fun i => (xs i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observations n H arguments raw xs).subst (fun a => emb (.var (j a))) = _
  rw [observationsSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SyntaxProof
