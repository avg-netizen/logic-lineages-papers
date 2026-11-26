module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalExistentialRankResultDefinitions
/-- Forget fixed numeric rank witnesses, retaining their actual graph evidence. -/
def ActualFixedEmbedding : Prop := ∀ (leaf : Program 4) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (s t parameter oldS oldT before after : OTerm alpha),
 Nonempty (Derivation body Delta ((OriginalLambdaOriginalRankDefinitions.Result leaf s t parameter oldS oldT before after).imp
  (Result leaf s t parameter oldS oldT)))
/-- ORIGINAL application function-side strictness, with identical actual argument.
The parent ranks are queried/bound internally, never caller premises. No leaf
certificate introduction or erased-parent equality is asserted. -/
def ActualApplicationFunctionLift : Prop := ∀ (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (input out d e fn fnOut arg : OTerm alpha),
 Nonempty (Derivation body Delta ((graph4 application input d e fn arg ⊓
  (graph4 application out d e fnOut arg ⊓ RankWitness fn fnOut)).imp (RankWitness input out)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultTargets
