module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc hopCertified)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph actualCalls)

/-- The exact original certified hop bytes, true raw callback, and two
successful least callbacks. Source/destination encoded states are
successors, so failure code zero cannot pay either minimum equality. -/
def hopCalls {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target q w r : OTerm α) : Formula α :=
  hopCertified hop target q w r ⊓ actualCalls raw least ctx ty current target q w r

/-- Exact scope: same raw hop; only the underlying source term, raw
witness, and underlying destination term are bound, in q/w/r order. -/
def hopCallRow {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target : OTerm α) : Formula (α ⊕ Fin 3) :=
  let j : α → α ⊕ Fin 3 := Sum.inl
  hopCalls raw least (ctx.relabel j) (ty.relabel j) (current.relabel j)
    (hop.relabel j) (target.relabel j) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

def someHopCalls {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop target : OTerm α) : Formula α :=
  block (hopCallRow raw least ctx ty current hop target)

/-- Recover the actual witnesses without assuming a parsed hop or a
true callback. Conversely the actual reported values suffice to
produce this same genuine selected advance result. -/
def OpenSuccessfulAdvanceCalls : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty current hop target : OTerm α),
    let accepted := selectedGraph raw least (suc target) ctx ty (suc current) hop
    let reported := someHopCalls raw least ctx ty current hop target
    Nonempty (Derivation body [] ((accepted.imp reported) ⊓ (reported.imp accepted)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
