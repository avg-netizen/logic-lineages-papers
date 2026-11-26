module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt finishAt)

/-- A genuine original scalar raw-code certificate, bound in the
object calculus, for the same selected positive program. -/
def supplied {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source target : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  existsOne (positiveAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
    (.var (.inr 0)) (target.relabel j))

def composeAt {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source first mid second target : OTerm α) : Formula α :=
  (finishAt raw least ctx ty source first mid ⊓ positiveAt raw least ctx ty mid second target).imp
    (supplied raw least ctx ty source target)

/-- The true sparse-field induction motive quantifies all source,
middle, second certificate and destination terms with the same
fixed packed context and type and the actual first raw certificate. -/
def uniformAt {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty first : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 4 := Sum.inl
  let source : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let mid : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let second : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let target : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  allBlock (composeAt raw least (ctx.relabel j) (ty.relabel j) source (first.relabel j)
    mid second target)

/-- The first actual chosen finish may be nil. The second is genuine
positive acceptance, and the result contains an actual positive raw
witness, not a pair of old certificate formulas. -/
def OpenFinishThenPositive : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty first : OTerm α),
    Nonempty (Derivation body [] (uniformAt raw least ctx ty first))

/-- Same original selected callback programs and fiber throughout,
no external interpretation or witness-synthesis oracle as a premise. -/
def OpenPositiveTransitivity : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty source first mid second target : OTerm α),
    let inputs := positiveAt raw least ctx ty source first mid ⊓ positiveAt raw least ctx ty mid second target
    Nonempty (Derivation body [] (inputs.imp (supplied raw least ctx ty source target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTargets
