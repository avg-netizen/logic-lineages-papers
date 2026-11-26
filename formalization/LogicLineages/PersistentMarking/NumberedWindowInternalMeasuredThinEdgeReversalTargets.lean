module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (exchangeTape edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (compareOptions guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)

def ExactOptionReversal : Prop :=
  ∀ (C : Program 3) (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (a b : OTerm α), Nonempty (Derivation body Γ
      ((programGraph (compareOptions C s) (suc z) (exchangeTape a b)).imp
        (programGraph (compareOptions C s) (suc z) (exchangeTape b a))))

def ExactPairedEdgeReversal : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b : OTerm α),
    let X := guardedExchange C s (pairedExchange baseX)
    Nonempty (Derivation body Γ ((acceptEdge (edge4 X W) ctx ty a b).imp
      (acceptEdge (edge4 X W) ctx ty b a)))

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalTargets
