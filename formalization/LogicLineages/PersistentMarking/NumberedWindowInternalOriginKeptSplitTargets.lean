module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

/-- The four witnesses are scratch tapes, not sets. All reports compare
the original actual joined tape, so repeated occurrences are retained. -/
def piece (whole left right joined : OTerm α) : Formula α :=
  programGraph append joined ![left,right] ⊓ programGraph permutation (suc z) ![whole,joined]

def evidence (left right kept removed : OTerm α) (w : Fin 8 → OTerm α) : Formula α :=
  piece left (w 0) (w 1) (w 4) ⊓
    (piece right (w 2) (w 3) (w 5) ⊓
      (piece kept (w 0) (w 2) (w 6) ⊓ piece removed (w 1) (w 3) (w 7)))

def matrix (left right kept removed : OTerm α) : Formula (α ⊕ Fin 8) :=
  evidence (left.relabel Sum.inl) (right.relabel Sum.inl) (kept.relabel Sum.inl)
    (removed.relabel Sum.inl) (fun i => .var (.inr i))

def splitExists (left right kept removed : OTerm α) : Formula α :=
  block (matrix left right kept removed)

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitTargets
