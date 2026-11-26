module
public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets

open NumberedWindowExchangeAtoms (HeadPairs allowed)
open NumberedWindowExchangeAlgorithm (row bits)
open NumberedWindowScalarAlgorithm (Settings edge)

/-- Symmetry is about the actual unordered use of the supplied pairs.
Their order and multiplicity in the numeric table may be arbitrary. -/
def HeadPairsSymmetric (pairs : HeadPairs) : Prop :=
  ∀ a b, allowed pairs a b = allowed pairs b a

def ExactRawRowSymmetry : Prop :=
  ∀ pairs : HeadPairs, HeadPairsSymmetric pairs → ∀ a b, row pairs a b = row pairs b a

/-- Both original term and argument-list bits, on all natural inputs. -/
def ExactRawExchangeSymmetry : Prop :=
  ∀ pairs : HeadPairs, HeadPairsSymmetric pairs → ∀ a b, bits pairs a b = bits pairs b a

/-- The two endpoints still pass the same original window and lexical guards. -/
def ExactScalarEdgeSymmetry : Prop :=
  ∀ s : Settings, HeadPairsSymmetric s.equivalentHeads →
    ∀ (ctx : List Nat) (ty a b : Nat), edge s ctx ty a b = edge s ctx ty b a

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
