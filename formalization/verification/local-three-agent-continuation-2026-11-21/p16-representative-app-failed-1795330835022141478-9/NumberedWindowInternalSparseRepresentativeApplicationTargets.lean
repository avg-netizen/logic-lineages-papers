module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseStructuralApplicationTargets (FunctionEdgeAt)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary suc)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseApplicationOutputCore (selectedLeast)
open NumberedWindowInternalSparseRoundObservationTargets (observed)

/-- Reorder the physical application tape to let the finite round vary just its
function coordinate. The last frontend slot is unused by selectedLeast. -/
def applicationObserver (least : Program 3) : Program 5 :=
  .composition (selectedLeast least) ![.projection 1,.projection 2,.projection 3,.projection 0,.projection 4,.projection 0]

def guards (C : Program 3) (s : Settings) (W : Program 3) {α : Type} (ctx cod a b : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let t : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  (windowAt W ctx cod a ⊓ windowAt W ctx cod b) ⊓ existsOne
    (unary (coverOption C s) t (a.relabel j) ⊓ unary (coverOption C s) t (b.relabel j))

def supportRow (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) {α : Type}
    (ctx dom cod arg value : OTerm α) : Formula (α ⊕ Fin 2) :=
  let j : α → α ⊕ Fin 2 := Sum.inl
  let f : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let g : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let a := auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j)
  let b := auxiliaryTerm (dom.relabel j) (cod.relabel j) g (arg.relabel j)
  (acceptEdge (edge4 X W) (ctx.relabel j) ((rawCons dom cod).relabel j) f g ⊓
    leastGraph C X W s (ctx.relabel j) (cod.relabel j) a (value.relabel j)).imp
      (guards C s W (ctx.relabel j) (cod.relabel j) a b)

def supports (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) {α : Type}
    (ctx dom cod arg value : OTerm α) : Formula α := allBlock (supportRow C X W s ctx dom cod arg value)

def ExactApplicationObservation : Prop :=
  ∀ (least : Program 3) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg f out : OTerm α),
    Nonempty (Derivation body Γ (observed (applicationObserver least) ctx dom cod arg f out)) ↔
    Nonempty (Derivation body Γ (programGraph least out ![ctx,cod,auxiliaryTerm dom cod f arg]))

/-- Replacing a function seed by its selected representative preserves a
successful application result, under the displayed original window and
common-cover condition for the fixed argument and result. -/
def ApplicationAt (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg f repr value : OTerm α),
    let initial := leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) value
    let chosen := leastGraph C X W s ctx (rawCons dom cod) f repr
    let final := leastGraph C X W s ctx cod (auxiliaryTerm dom cod repr arg) value
    Nonempty (Derivation body Γ ((supports C X W s ctx dom cod arg value ⊓ (initial ⊓ chosen)).imp final))

def ExactRepresentativeApplication : Prop :=
  ∀ (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3), FunctionEdgeAt C s X W → ApplicationAt C s X W

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationTargets
