module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args5 equivalent)

/-- The actual initial current is successor(source); the same original
certificate is the raw initial cursor and the chosen fuel. The result is
the genuine successful successor(target), not an equality of failures. -/
def targetScratchRow {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula (α ⊕ Fin 1) :=
  let state : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let cert := certificate.relabel j
  loopGraph raw least state cert (ctx.relabel j) (ty.relabel j) (suc (source.relabel j)) cert ⊓
    scratchGraph state z (suc (target.relabel j))

def successfulTerminal {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula α :=
  existsOne (targetScratchRow raw least ctx ty source certificate target)

/-- No caller-supplied terminal result, arithmetic bound, typed
callback invariant, or semantic interpretation is a premise. Source
shape and a successful terminal graph are exactly what acceptance
says for this same original selected program on arbitrary free terms. -/
def OpenPositiveCharacterization : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty source certificate target : OTerm α),
    let a := programGraph (positive raw least) (suc z) (args5 ctx ty source certificate target)
    let b := (equal certificate z).not ⊓ successfulTerminal raw least ctx ty source certificate target
    Nonempty (Derivation body [] (equivalent a b))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationTargets
