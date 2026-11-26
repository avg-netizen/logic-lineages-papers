module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (decodeNumbers numbersNumber)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseDirectedFilter

/-- Every standard scratch code and actual edge AST, with the literal
source-directed advance on the two independently decoded ordered lists. -/
def ExactAllInputDirectedFilter : Prop :=
  ∀ (E : Program 4) (vertices seen ctx ty : Nat),
    evaluate (pass E) (List.Vector.ofFn (passTape vertices seen ctx ty)) =
      numbersNumber (NumberedWindowClassAlgorithm.advance
        (fun w v => decide (evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1))
        ((decodeNumbers vertices).getD []) ((decodeNumbers seen).getD []))

/-- A physical input cons and its actual filtered output expose one
genuine filtered tail and the literal retain/skip object disjunction. -/
def ExactOpenDirectedFilterCons : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices h tail seen ctx ty out : OTerm α),
    Nonempty (Derivation body Γ
      ((cell vertices h tail ⊓ passGraph E out vertices seen ctx ty).imp
        (restReport E out h tail seen ctx ty)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
