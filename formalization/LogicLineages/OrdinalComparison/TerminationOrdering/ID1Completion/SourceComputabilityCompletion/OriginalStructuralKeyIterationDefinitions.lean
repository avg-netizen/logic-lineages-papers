module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIteration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalGraphComposition
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Parameter-sensitive structural-key iteration. Literal Programs only; preservation is a theorem supplier, not a field. -/
structure Data where
  representative : Program 2
  valid : Program 2
  condition : Program 2
  observer : Program 2

def step (data : Data) : Program 2 :=
  InternalParameterizedBoundedDescentNormalizer.transition data.representative data.valid

def activeGraph {α : Type} (data : Data) (input parameter : OTerm α) : Formula α :=
  graph2 data.condition
    InternalOriginalStepGuard.one input parameter

def markGraph {α : Type} (data : Data) (mark input parameter : OTerm α) : Formula α :=
  graph2 data.observer mark input parameter

/-- A uniform independent internal supplier for the actual bounded-descent transition. -/
def Preservation (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (out input parameter indicator : OTerm α),
    Nonempty (Derivation body Gamma (activeGraph data input parameter)) →
    Nonempty (Derivation body Gamma (graph2 (step data) out input parameter)) →
    Nonempty (Derivation body Gamma ((markGraph data indicator out parameter).iff (markGraph data indicator input parameter)))

/-- The caller pays source validity from its unchanged arithmetic condition. -/
def Validity (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (input parameter : OTerm α),
    Nonempty (Derivation body Gamma (activeGraph data input parameter)) →
    Nonempty (Derivation body Gamma (graph2 data.valid InternalOriginalStepGuard.one input parameter))

/-- Every ACTUAL transition preserves the caller's condition internally. -/
def Closure (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (out input parameter : OTerm α),
    Nonempty (Derivation body Gamma (activeGraph data input parameter)) →
    Nonempty (Derivation body Gamma (graph2 (step data) out input parameter)) →
    Nonempty (Derivation body Gamma (activeGraph data out parameter))

def iterationBody {α : Type} (data : Data) (count : OTerm α) : Formula (α ⊕ Fin 4) :=
  (InternalParameterizedNumericIteration.repeatGraph (step data)
    (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)) ⊓
    (activeGraph data (.var (.inr 0)) (.var (.inr 2)) ⊓
      markGraph data (.var (.inr 3)) (.var (.inr 0)) (.var (.inr 2)))).imp
    (markGraph data (.var (.inr 3)) (.var (.inr 1)) (.var (.inr 2)))

def iterationRow {α : Type} (data : Data) (count : OTerm α) : Formula α :=
  allBlock (iterationBody data count)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIteration
