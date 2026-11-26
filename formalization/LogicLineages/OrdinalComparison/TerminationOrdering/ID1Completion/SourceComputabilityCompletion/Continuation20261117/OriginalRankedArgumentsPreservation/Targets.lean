module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedArgumentsPreservation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine homogeneous typed-entry permutation transport for the ranked-head
argument list. The literal original guarded checker, its raw+1 fuel, context,
concrete H and fixed M/W policies remain unchanged on both sides. No target
success, encoded image, native reflection or preservation oracle is assumed.
M/W are fixed before runtime and may be arbitrary: permutation retains each
entire (type,term-code) entry and hence its SAME local term checks. -/
def InternalHomogeneousArgumentsPreserved : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (M W : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (count types base target gamma context : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.argumentsCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![types,base,gamma,context])) →
  Nonempty (Derivation body Delta
    (graph2 Continuation20261114.OriginalArgumentPermutation.check (suc z) base target)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalUniverseDecoder.argumentsCheck
      (Continuation20261116.OriginalConcreteHeadSignature.signature n arity) M W)
      (suc z) ![types,target,gamma,context]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedArgumentsPreservation.Targets
