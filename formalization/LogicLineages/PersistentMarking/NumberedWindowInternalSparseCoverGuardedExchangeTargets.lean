module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowCoverBoundsAlgorithm (cover)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

def optionAtSlot (C : Program 3) (s : Settings) (i : Fin 2) : Program 2 :=
  .composition (coverOption C s) (fun _ : Fin 1 => .projection i)

def compareOptions (C : Program 3) (s : Settings) : Program 2 :=
  .composition equalityTest ![optionAtSlot C s 0,optionAtSlot C s 1]

def guardedExchange (C : Program 3) (s : Settings) (X : Program 2) : Program 2 :=
  conjunction X (compareOptions C s)

def ExactOriginalExchangeCoverOption : Prop :=
  ∀ (hp : HeadPairs) (heads types : List Nat) (a b : Nat), (bits hp a b).1 = true →
    cover heads types a = cover heads types b

def ExactGuardedExchangeCalibration : Prop :=
  ∀ (C : Program 3) (s : Settings) (X : Program 2), ActualSelectedCoverOutput C →
    ActualTermExchange s X → ActualTermExchange s (guardedExchange C s X)

/-- Open integer equality of the two true optional callback outputs. Both
accepted exchange and the two graph occurrences use the original seeds. -/
def ExactGuardedExchangeOptionEquality : Prop :=
  ∀ (C : Program 3) (s : Settings) (X : Program 2) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (a b x y : OTerm α),
    let accept := programGraph (guardedExchange C s X) (suc z) (exchangeTape a b)
    let outputs := unary (coverOption C s) x a ⊓ unary (coverOption C s) y b
    Nonempty (Derivation body Γ ((accept ⊓ outputs).imp (eqn x y)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeTargets
