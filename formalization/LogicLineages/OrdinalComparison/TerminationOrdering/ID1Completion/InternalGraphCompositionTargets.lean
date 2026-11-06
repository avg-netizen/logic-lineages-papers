module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalFiniteBlocks

def ActualOriginalCompositionInstance : Prop :=
  ∀ (m n : Nat) (α : Type) (f : OFormula (Fin (n+1))) (g : Fin n → OFormula (Fin (m+1)))
    (out : OTerm α) (xs : Fin m → OTerm α),
  graph (OrdinaryArithmetic.compositionGraph f g) out xs =
    block (arithmeticEmbedding.onFormula (matrix f g out xs))

def ActualOriginalCompositionIntroduction : Prop :=
  ∀ (body : Positive (Fin 1)) (m n : Nat) (α : Type) (Gamma : List (Formula α))
    (f : OFormula (Fin (n+1))) (g : Fin n → OFormula (Fin (m+1)))
    (out : OTerm α) (xs : Fin m → OTerm α) (ys : Fin n → OTerm α),
  Nonempty (Derivation body Gamma (graph f out ys)) →
  (∀ i, Nonempty (Derivation body Gamma (graph (g i) (ys i) xs))) →
  Nonempty (Derivation body Gamma (graph (OrdinaryArithmetic.compositionGraph f g) out xs))

def ActualOriginalCompositionElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (m n : Nat) (α : Type) (Gamma : List (Formula α))
    (f : OFormula (Fin (n+1))) (g : Fin n → OFormula (Fin (m+1)))
    (out : OTerm α) (xs : Fin m → OTerm α) (psi : Formula α),
  Nonempty (Derivation body Gamma (graph (OrdinaryArithmetic.compositionGraph f g) out xs)) →
  Nonempty (Derivation body (arithmeticEmbedding.onFormula (matrix f g out xs) ::
    Gamma.map (fun p => p.relabel Sum.inl)) (psi.relabel Sum.inl)) →
  Nonempty (Derivation body Gamma psi)

def ActualOriginalCompositionTotality : Prop :=
  ∀ (body : Positive (Fin 1)) (m n : Nat) (f : OFormula (Fin (n+1)))
    (g : Fin n → OFormula (Fin (m+1))),
  Total body f → (∀ i, Total body (g i)) → Total body (OrdinaryArithmetic.compositionGraph f g)

def ActualOriginalCompositionFunctionality : Prop :=
  ∀ (body : Positive (Fin 1)) (m n : Nat) (f : OFormula (Fin (n+1)))
    (g : Fin n → OFormula (Fin (m+1))),
  Functional body f → (∀ i, Functional body (g i)) →
    Functional body (OrdinaryArithmetic.compositionGraph f g)

/-- The original compiler's composition constructor, with every component
proof obligation retained. This says nothing about its recursion constructor. -/
def ActualOriginalProgramComposition : Prop :=
  ∀ (body : Positive (Fin 1)) (m n : Nat)
    (f : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program n)
    (g : Fin n → LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program m),
  Total body (OrdinaryArithmetic.graphFormula f) →
  (∀ i, Total body (OrdinaryArithmetic.graphFormula (g i))) →
  Functional body (OrdinaryArithmetic.graphFormula f) →
  (∀ i, Functional body (OrdinaryArithmetic.graphFormula (g i))) →
  Total body (OrdinaryArithmetic.graphFormula (.composition f g)) ∧
    Functional body (OrdinaryArithmetic.graphFormula (.composition f g))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTargets
