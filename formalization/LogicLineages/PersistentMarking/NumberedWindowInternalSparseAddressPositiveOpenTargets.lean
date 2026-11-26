module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparseAddressPositive (addressPositive)

/-- Actual well-formed physical tag3/arity3 report at the unchanged
input address, not raw numeric validity of its class by itself. -/
def addressReport {α : Type} (address ctx ty cls : OTerm α) : Formula α :=
  unary addressGood (suc z) address ⊓
    (unary rawContext ctx address ⊓
      (unary rawResult ty address ⊓ unary rawLeast cls address))

def witnessData {α : Type} (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right ctx ty src dst : OTerm α) : Formula α :=
  addressReport left ctx ty src ⊓
    (addressReport right ctx ty dst ⊓
      (unary ctxValid (suc z) ctx ⊓
        (unary tyValid (suc z) ty ⊓
          programGraph (positive raw least) (suc z) ![ctx,ty,src,cert,dst])))

def witnessRow {α : Type} (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right : OTerm α) : Formula (α ⊕ Fin 4) :=
  let j : α → α ⊕ Fin 4 := Sum.inl
  witnessData ctxValid tyValid raw least (left.relabel j) (cert.relabel j) (right.relabel j)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))

def someAddressPositive {α : Type} (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3)
    (left cert right : OTerm α) : Formula α :=
  block (witnessRow ctxValid tyValid raw least left cert right)

/-- Genuine arbitrary-open graph equivalence for the newly selected
same-tape address checker: actual paired reports share one packed
context/type, whose real guard graph outputs are one, and the selected
same-fiber fold accepts the same certificate. No callback
interpretation or replacement of a previously installed sourceBody. -/
def OpenAddressPositive : Prop :=
  ∀ (body : Positive (Fin 1)) (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3)
    (α : Type) (left cert right : OTerm α),
    let accepted := programGraph (addressPositive ctxValid tyValid raw least) (suc z) ![left,cert,right]
    let reported := someAddressPositive ctxValid tyValid raw least left cert right
    Nonempty (Derivation body [] ((accepted.imp reported) ⊓ (reported.imp accepted)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
