module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)
open OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalUniverseDecoderInternalAcceptance OriginalUniverseDecoderInternalAcceptanceSyntaxProof
open OriginalInternalJobAdmissible
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalInternalJobAdmissibleSyntaxProof

theorem admissibleSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (role typ raw gamma c : OTerm alpha) (ts : alpha → OTerm beta) :
 (Admissible H M W role typ raw gamma c).subst (fun a => emb (ts a)) =
 Admissible H M W (role.subst ts) (typ.subst ts) (raw.subst ts) (gamma.subst ts) (c.subst ts) := by
 simp only [Admissible,orSubst,InternalRecursionClosureSyntaxProof.conjunctionSubst,
  equalSubst,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedSubst,
  argumentsWitnessSubst,numeralSubst]
theorem admissibleRename {beta : Type} (H : Program 1) (M W : Program 2)
 (role typ raw gamma c : OTerm alpha) (j : alpha → beta) :
 (Admissible H M W role typ raw gamma c).relabel j =
 Admissible H M W (role.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Admissible H M W role typ raw gamma c).subst (fun a => emb (.var (j a))) = _
 rw [admissibleSubst]
 simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
