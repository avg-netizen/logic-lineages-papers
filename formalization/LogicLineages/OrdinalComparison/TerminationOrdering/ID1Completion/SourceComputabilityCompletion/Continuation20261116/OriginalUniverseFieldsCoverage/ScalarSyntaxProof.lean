module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ScalarSyntaxProof
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

theorem fieldsSubst {beta : Type} (n : Nat) (raw count types heads labels bound : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (OriginalEnumerationFields.Targets.accepted n raw count types heads labels bound).subst (fun a => emb (ts a)) =
      OriginalEnumerationFields.Targets.accepted n (raw.subst ts) (count.subst ts) (types.subst ts)
        (heads.subst ts) (labels.subst ts) (bound.subst ts) := by
  have hv : (fun i => (![raw,count,types,heads,labels,bound] i).subst ts) =
      ![raw.subst ts,count.subst ts,types.subst ts,heads.subst ts,labels.subst ts,bound.subst ts] := by
    funext i; fin_cases i <;> rfl
  simp only [OriginalEnumerationFields.Targets.accepted,InternalComputabilityApplicationSyntaxProof.programSubst,
    numeral,zSubst,sucSubst,hv]

theorem acceptedSubst {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (typ raw gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (accepted n arity H arguments typ raw gamma context).subst (fun a => emb (ts a)) =
      accepted n arity H arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) (context.subst ts) := by
  cases arguments <;> simp only [accepted,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedSubst,
    OriginalUniverseDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedSubst,Bool.false_eq_true,if_true,if_false]

theorem observationsSubst {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) (ts : alpha → OTerm beta) :
    (observations n arity H arguments raw xs).subst (fun a => emb (ts a)) =
      observations n arity H arguments (raw.subst ts) (fun i => (xs i).subst ts) := by
  simp only [observations,conjunctionSubst,acceptedSubst,
    Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof.closureSubst,
    graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ScalarSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ScalarSyntaxProof
