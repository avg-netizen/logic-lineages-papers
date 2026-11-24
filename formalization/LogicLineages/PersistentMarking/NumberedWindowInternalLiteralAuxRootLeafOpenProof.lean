module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionRecover)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (shapes)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem rejectOther (leaf : Nat → Program 3) (tag : Nat) (ht : tag < 6)
    (xs : Fin 3 → OTerm α) (aux : D B Γ (bit sourceIsAux xs))
    (held : D B Γ (bit (leafAtAuxiliary leaf tag) xs)) : D B Γ (⊥ : Formula α) := by
  simp only [leafAtAuxiliary,if_pos ht] at held
  have bad := successorBranchElim sourceIsAux (leaf tag) (constantZero 3) (suc z) z xs aux held
  obtain ⟨err⟩ := valueUnique (constantZero 3) (suc z) z xs bad (constantZeroValue xs)
  exact ⟨sucNeZeroApply err⟩

theorem betaFacts (leaf : Nat → Program 3) (xs : Fin 3 → OTerm α)
    (aux : D B Γ (bit sourceIsAux xs)) (held : D B Γ (bit (leafAtAuxiliary leaf 6) xs)) :
    D B Γ (bit (leaf 6) xs ⊓ bit functionLambdaHeader xs) := by
  have branch := successorBranchElim sourceIsAux (leaf 6) (conjunction (leaf 6) functionLambdaHeader)
    (suc z) z xs aux held
  exact conjunctionRecover (leaf 6) functionLambdaHeader xs branch

theorem bottomFacts (leaf : Nat → Program 3) (xs : Fin 3 → OTerm α)
    (aux : D B Γ (bit sourceIsAux xs)) (held : D B Γ (bit (leafAtAuxiliary leaf 7) xs)) :
    D B Γ (bit (leaf 7) xs ⊓ bit targetBottom xs) := by
  have branch := successorBranchElim sourceIsAux (leaf 7) (conjunction (leaf 7) targetBottom)
    (suc z) z xs aux held
  exact conjunctionRecover (leaf 7) targetBottom xs branch

/-- A successful actual auxiliary root has exactly the two possible
root tags: beta with a lambda-header report, or bottom with its actual
raw target equality test. The six other physical leaves cannot accept. -/
theorem exact_OpenAuxiliaryRootLeafCases (leaf : Nat → Program 3) (tag arity : Nat)
    (inShapes : (tag,arity) ∈ shapes) (xs : Fin 3 → OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux xs)) (held : D B Γ (bit (leafAtAuxiliary leaf tag) xs))
    (beta : D B Γ (bit (leaf 6) xs) → D B Γ (bit functionLambdaHeader xs) → D B Γ goal)
    (bottom : D B Γ (bit (leaf 7) xs) → D B Γ (bit targetBottom xs) → D B Γ goal) :
    D B Γ goal := by
  have narrow : tag < 6 ∨ tag = 6 ∨ tag = 7 := by
    simp only [shapes,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at inShapes
    rcases inShapes with h | h | h | h | h | h | h | h <;> omega
  rcases narrow with low | eq | eq
  · exact (rejectOther leaf tag low xs aux held).map Derivation.explosion
  · subst tag
    obtain ⟨h⟩ := betaFacts leaf xs aux held
    exact beta ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  · subst tag
    obtain ⟨h⟩ := bottomFacts leaf xs aux held
    exact bottom ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩

#print axioms exact_OpenAuxiliaryRootLeafCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafOpenProof
