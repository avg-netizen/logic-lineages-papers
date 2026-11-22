module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumTargets
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (exchangeTape edge4)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (compareOptions guardedExchange)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)

def swapExchange (X : Program 2) : Program 2 := .composition X ![.projection 1,.projection 0]

def pairedExchange (X : Program 2) : Program 2 := conjunction X (swapExchange X)

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

def EdgeMinimumEqualityAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b x y : OTerm α),
    let members := leastGraph C X W s ctx ty a x ⊓ leastGraph C X W s ctx ty b y
    Nonempty (Derivation body Γ ((members ⊓ acceptEdge (edge4 X W) ctx ty a b).imp (eqn x y)))

def ExactPairedEdgeMinimumEquality : Prop :=
  ∀ (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3),
    EdgeMinimumEqualityAt C (guardedExchange C s (pairedExchange baseX)) W s

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSymmetricExchangeTargets
