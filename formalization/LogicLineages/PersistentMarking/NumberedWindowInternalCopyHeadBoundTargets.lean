module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadConeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadBoundTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowCopyAlgorithm (Entries rank)
open NumberedWindowInternalConstructorHeadFiniteTargets (D)

def ExactOriginalFiniteCopyHeadRank : Prop :=
  ∀ (entries : Entries) (head value : Nat),
    rank entries head = some value → value < entries.length + 2

def ExactOriginalObjectFiniteCopyHeadRank : Prop :=
  ∀ (entries : Entries) (head value : Nat) (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)),
    rank entries head = some value →
    D B Γ (ltF (numeral value) (numeral (entries.length + 2)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadBoundTargets
