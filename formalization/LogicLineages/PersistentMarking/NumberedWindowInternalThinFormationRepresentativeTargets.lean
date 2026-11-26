module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)

/-- For this argument, context, domain and codomain, actual admitted functions
give actual admitted applications. This single local typing obligation is
independent of the exchange payload, minimum and particular result. -/
def formation {α : Type} (W : Program 3) (ctx dom cod arg : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f).imp
    (windowAt W (ctx.relabel j) (cod.relabel j) (auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j))))

def RepresentativeAt (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg f repr value : OTerm α),
    let initial := leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) value
    let chosen := leastGraph C X W s ctx (rawCons dom cod) f repr
    let final := leastGraph C X W s ctx cod (auxiliaryTerm dom cod repr arg) value
    Nonempty (Derivation body Γ ((formation W ctx dom cod arg ⊓ (initial ⊓ chosen)).imp final))

end LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeTargets
