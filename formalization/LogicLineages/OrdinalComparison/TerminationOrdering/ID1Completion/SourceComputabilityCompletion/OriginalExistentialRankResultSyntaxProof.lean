module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)
open OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalExistentialRankResultDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalLambdaOriginalRankDefinitions (PackedRankDrop)
theorem dropSubst {beta : Type} (s t before after : OTerm alpha) (ts : alpha → OTerm beta) :
 (PackedRankDrop s t before after).subst (fun a => emb (ts a)) =
 PackedRankDrop (s.subst ts) (t.subst ts) (before.subst ts) (after.subst ts) := by
 simp only [PackedRankDrop,conjunctionSubst,graph1,programSubst,consTermSubst,emptySubst,
  InternalLessThan.strictLess,InternalQuotientComparisonSyntaxProof.orderSubst]

theorem afterSubst {beta : Type} (s t before : OTerm alpha) (ts : alpha → OTerm beta) :
 (AfterWitness s t before).subst (fun a => emb (ts a)) =
 AfterWitness (s.subst ts) (t.subst ts) (before.subst ts) := by
 unfold AfterWitness
 rw [existsSubst,liftedEmbedding]
 unfold AfterMatrix
 simp only [dropSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem rankSubst {beta : Type} (s t : OTerm alpha) (ts : alpha → OTerm beta) :
 (RankWitness s t).subst (fun a => emb (ts a)) = RankWitness (s.subst ts) (t.subst ts) := by
 unfold RankWitness
 rw [existsSubst,liftedEmbedding]
 unfold BeforeMatrix
 simp only [afterSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem afterRename {beta : Type} (s t before : OTerm alpha) (j : alpha → beta) :
 (AfterWitness s t before).relabel j = AfterWitness (s.relabel j) (t.relabel j) (before.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AfterWitness s t before).subst (fun a => emb (.var (j a))) = _
 rw [afterSubst]
 simp only [← termRelabelAsSubst]

theorem rankWitnessRename {beta : Type} (s t : OTerm alpha) (j : alpha → beta) :
 (RankWitness s t).relabel j = RankWitness (s.relabel j) (t.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (RankWitness s t).subst (fun a => emb (.var (j a))) = _
 rw [rankSubst]
 simp only [← termRelabelAsSubst]

theorem afterInstantiate (s t before after : OTerm alpha) :
 instantiate (AfterMatrix s t before) (emb after) = PackedRankDrop s t before after := by
 rw [instantiate,bindEmbedding]
 unfold AfterMatrix
 rw [dropSubst]
 simp only [varBind,liftBind]

theorem beforeInstantiate (s t before : OTerm alpha) :
 instantiate (BeforeMatrix s t) (emb before) = AfterWitness s t before := by
 rw [instantiate,bindEmbedding]
 unfold BeforeMatrix
 rw [afterSubst]
 simp only [varBind,liftBind]

theorem afterIntro (s t before after : OTerm alpha)
 (h : Nonempty (Derivation body Delta (PackedRankDrop s t before after))) :
 Nonempty (Derivation body Delta (AfterWitness s t before)) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialIntroduction (emb after)
 rw [afterInstantiate]
 exact h

theorem rankIntro (s t before after : OTerm alpha)
 (h : Nonempty (Derivation body Delta (PackedRankDrop s t before after))) :
 Nonempty (Derivation body Delta (RankWitness s t)) := by
 obtain ⟨hh⟩ := afterIntro s t before after h
 apply Nonempty.intro
 apply Derivation.existentialIntroduction (emb before)
 rw [beforeInstantiate]
 exact hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
