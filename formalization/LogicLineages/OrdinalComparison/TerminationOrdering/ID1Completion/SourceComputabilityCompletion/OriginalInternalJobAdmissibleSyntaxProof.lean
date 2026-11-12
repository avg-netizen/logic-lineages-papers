module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
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
theorem argumentsWitnessSubst {beta : Type} (H : Program 1) (M W : Program 2)
 (raw gamma c : OTerm alpha) (ts : alpha → OTerm beta) :
 (ArgumentsWitness H M W raw gamma c).subst (fun a => emb (ts a)) =
 ArgumentsWitness H M W (raw.subst ts) (gamma.subst ts) (c.subst ts) := by
 unfold ArgumentsWitness
 rw [existsSubst,InternalRecursionClosureSyntaxProof.liftedEmbedding]
 unfold ArgumentsMatrix
 simp only [argumentsAcceptedSubst,InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr] <;> rfl
theorem argumentsWitnessRename {beta : Type} (H : Program 1) (M W : Program 2)
 (raw gamma c : OTerm alpha) (j : alpha → beta) :
 (ArgumentsWitness H M W raw gamma c).relabel j =
 ArgumentsWitness H M W (raw.relabel j) (gamma.relabel j) (c.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (ArgumentsWitness H M W raw gamma c).subst (fun a => emb (.var (j a))) = _
 rw [argumentsWitnessSubst]
 simp only [← termRelabelAsSubst]
theorem argumentsInstantiate (H : Program 1) (M W : Program 2)
 (raw gamma c types : OTerm alpha) :
 instantiate (ArgumentsMatrix H M W raw gamma c) (emb types) =
 ArgumentsAccepted H M W types raw gamma c := by
 rw [instantiate,bindEmbedding]
 unfold ArgumentsMatrix
 rw [argumentsAcceptedSubst]
 simp only [varBind,liftBind]
theorem argumentsIntro (H : Program 1) (M W : Program 2)
 (raw gamma c types : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c))) :
 Nonempty (Derivation body Delta (ArgumentsWitness H M W raw gamma c)) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialIntroduction (emb types)
 rw [argumentsInstantiate]
 exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
