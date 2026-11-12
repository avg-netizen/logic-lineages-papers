module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIteration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalGraphComposition
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side arbitrary transition, condition and indexed observer. No runtime
selection is modified; closure and preservation remain explicit suppliers. -/
structure Data where
  transition : Program 2
  condition : Program 2
  observer : Program 3

def step (data : Data) : Program 2 :=
  data.transition

def activeGraph {α : Type} (data : Data) (input parameter : OTerm α) : Formula α :=
  graph2 data.condition
    InternalOriginalStepGuard.one input parameter

def markGraph {α : Type} (data : Data) (mark input parameter cutoff : OTerm α) : Formula α :=
  graph3 data.observer mark cutoff input parameter

/-- A uniform independent internal supplier for the supplied literal transition. -/
def Preservation (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (out input parameter indicator cutoff : OTerm α),
    Nonempty (Derivation body Gamma (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)) →
    Nonempty (Derivation body Gamma (activeGraph data input parameter)) →
    Nonempty (Derivation body Gamma (graph2 (step data) out input parameter)) →
    Nonempty (Derivation body Gamma ((markGraph data indicator out parameter cutoff).iff (markGraph data indicator input parameter cutoff)))

/-- Every ACTUAL transition preserves the caller's condition internally. -/
def Closure (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (out input parameter : OTerm α),
    Nonempty (Derivation body Gamma (activeGraph data input parameter)) →
    Nonempty (Derivation body Gamma (graph2 (step data) out input parameter)) →
    Nonempty (Derivation body Gamma (activeGraph data out parameter))

def iterationBody {α : Type} (data : Data) (count : OTerm α) : Formula (α ⊕ Fin 5) :=
  (InternalParameterizedNumericIteration.repeatGraph (step data)
    (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)) ⊓
    (activeGraph data (.var (.inr 0)) (.var (.inr 2)) ⊓
      (OriginalIndexedObserverDefinitions.ActualRange (.var (.inr 4)) (.var (.inr 2)) ⊓
        markGraph data (.var (.inr 3)) (.var (.inr 0)) (.var (.inr 2)) (.var (.inr 4))))).imp
    (markGraph data (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 4)))

def iterationRow {α : Type} (data : Data) (count : OTerm α) : Formula α :=
  allBlock (iterationBody data count)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverIteration
