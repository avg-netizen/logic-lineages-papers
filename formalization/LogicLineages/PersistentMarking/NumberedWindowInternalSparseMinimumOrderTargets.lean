module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalLessThan (strictLess)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseOrderedMinimum (minimumStep)
open NumberedWindowInternalSparsePositiveOutputTargets (equivalent)

def update {α : Type} (h prior k : OTerm α) : Formula α :=
  programGraph minimumStep (suc k) ![h,prior]

/-- With no prior result the actual option-update graph returns the offered head. -/
def ExactOpenMinimumEmptyUpdate : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h k : OTerm α),
    Nonempty (Derivation body Γ (equivalent (update h z k) (eqn k h)))

/-- The comparison is on the unencoded head and earlier minimum. A strict
decrease chooses the head; ties and increases retain the previous value. -/
def ExactOpenMinimumOrderedUpdate : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h prior k : OTerm α),
    let selected := update h (suc prior) k
    Nonempty (Derivation body Γ
      (((strictLess h prior).imp (equivalent selected (eqn k h))) ⊓
        ((strictLess h prior).not.imp (equivalent selected (eqn k prior)))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderTargets
