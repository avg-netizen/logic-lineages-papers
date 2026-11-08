module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppend
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Step inputs are [head, recursively appended tail, suffix]. The original
list constructor preserves the head and the recursively appended tail. -/
def appendStep : Program 3 :=
  .composition InternalListCodec.consCode
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0))

/-- Inputs [prefix,suffix]. The base is the arbitrary suffix, and recursion
uses the unchanged original successor/pair raw-list codec on the prefix. -/
def append : Program 2 :=
  InternalRawListRecursion.listRec (.projection (0 : Fin 1)) appendStep

/-- The exact cons equation has one internal witness for the appended tail.
All list codes, heads and suffixes remain arbitrary object-language terms. -/
def appendConsStep {α : Type}
    (out head tail suffix : OrdinaryArithmetic.Term α) : Formula α :=
  existsOne
    (graph2 append (.var (.inr (0 : Fin 1)))
        (tail.relabel Sum.inl) (suffix.relabel Sum.inl) ⊓
      graph2 InternalListCodec.consCode (out.relabel Sum.inl)
        (head.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

/-- The original numeric code of status one and the empty worklist is two,
not one. This is the literal arithmetic numeral, not a new state encoding. -/
def successState {α : Type} : OrdinaryArithmetic.Term α :=
  OrdinaryArithmetic.succTerm (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)

/-- Success after the stated count in the ACTUAL frozen numeric stack
iterator. The existential initial state is constrained by the original pair
graph to have status one and the given raw worklist. No external execution,
decoded list, well-formedness, rank, leaf calibration or semantic validity is
part of this formula. An early success may consume unused fixed-point fuel. -/
def successfulWork {α : Type} (node leaf : Program 1)
    (count work : OrdinaryArithmetic.Term α) : Formula α :=
  existsOne
    (graph2 InternalPairing.pairing (.var (.inr (0 : Fin 1)))
        InternalOriginalStepGuard.one (work.relabel Sum.inl) ⊓
      graph2 (InternalApplicationValidityStack.iterate node leaf) successState
        (count.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppend
