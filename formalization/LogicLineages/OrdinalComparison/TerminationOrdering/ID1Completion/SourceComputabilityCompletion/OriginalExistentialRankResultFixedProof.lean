module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultFixedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalExistentialRankResultDefinitions OriginalExistentialRankResultSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalBetaTotalityProof (disjunctionElimination)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atResult (leaf : Program 4) (s t parameter oldS oldT before after : OTerm alpha)
 (h : Nonempty (Derivation body Delta (OriginalLambdaOriginalRankDefinitions.Result leaf s t parameter oldS oldT before after))) :
 Nonempty (Derivation body Delta (Result leaf s t parameter oldS oldT)) := by
 let A := equal s t ⊓ OriginalLambdaOriginalRankDefinitions.PackedRankDrop oldS oldT before after
 let B := OriginalLambdaErasureSquareDichotomyDefinitions.Witness leaf s t parameter
 have hl : Nonempty (Derivation body (A :: Delta) (Result leaf s t parameter oldS oldT)) := by
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := andIntro (andLeft ha) (rankIntro oldS oldT before after (andRight ha))
  exact ⟨orLeft he⟩
 have hr : Nonempty (Derivation body (B :: Delta) (Result leaf s t parameter oldS oldT)) :=
  ⟨orRight (Derivation.hypothesis List.mem_cons_self)⟩
 obtain ⟨h⟩ := h
 obtain ⟨hl⟩ := hl
 obtain ⟨hr⟩ := hr
 exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)⟩

theorem actualFixedEmbedding : OriginalExistentialRankResultTargets.ActualFixedEmbedding := by
 intro leaf body alpha Delta s t parameter oldS oldT before after
 apply Nonempty.intro
 apply Derivation.implicationIntroduction
 exact Classical.choice (atResult leaf s t parameter oldS oldT before after
  ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultFixedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultFixedProof
