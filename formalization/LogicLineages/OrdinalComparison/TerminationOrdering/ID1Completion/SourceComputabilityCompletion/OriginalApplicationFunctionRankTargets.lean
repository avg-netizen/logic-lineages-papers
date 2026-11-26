module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport

/-- Strict original variable rank lifts through the original packed application
constructor on its FUNCTION side, with the identical actual argument in both
parents. These are old endpoints, not erased or canonicalized endpoints. No
positive argument-step constructor or canonical collapse is asserted. -/
def ActualOriginalApplicationFunctionRank : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input out d e fn fnOut arg before after childBefore childAfter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph4 application input d e fn arg ⊓
      (graph4 application out d e fnOut arg ⊓
      (graph1 variableRankPackedRaw childBefore fn ⊓
      (graph1 variableRankPackedRaw childAfter fnOut ⊓
      (graph1 variableRankPackedRaw before input ⊓
      (graph1 variableRankPackedRaw after out ⊓
        InternalLessThan.strictLess childAfter childBefore)))))).imp
      (InternalLessThan.strictLess after before)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankTargets
