module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaOriginalRankDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem liftOriginalRanks (oldS oldT oldChildS oldChildT d e before after : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldS d e oldChildS)))
    (ht : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldT d e oldChildT)))
    (hr : Nonempty (Derivation body Delta (PackedRankDrop oldChildS oldChildT before after))) :
    Nonempty (Derivation body Delta (PackedRankDrop oldS oldT before after)) :=
  andIntro (OriginalFinalGuardedRankConstructorProof.lambdaValue oldS d e oldChildS before hs (andLeft hr))
    (andIntro (OriginalFinalGuardedRankConstructorProof.lambdaValue oldT d e oldChildT after ht (andLeft (andRight hr)))
      (andRight (andRight hr)))

theorem actualConstructorLift : ConstructorLift := by
  intro body alpha Delta oldS oldT oldChildS oldChildT d e before after
  let A := graph3 OriginalLambdaConstructor.constructor oldS d e oldChildS ⊓
    (graph3 OriginalLambdaConstructor.constructor oldT d e oldChildT ⊓
      PackedRankDrop oldChildS oldChildT before after)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ho⟩ := liftOriginalRanks oldS oldT oldChildS oldChildT d e before after
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction ho⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankProof
