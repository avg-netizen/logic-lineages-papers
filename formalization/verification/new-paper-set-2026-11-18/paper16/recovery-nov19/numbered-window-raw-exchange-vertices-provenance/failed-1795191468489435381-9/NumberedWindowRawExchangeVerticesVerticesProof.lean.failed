module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTermStepProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgsStepProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesExchangeTableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesVerticesProof
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowCoverBoundsAlgorithm (bounds cover)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowScalarAlgorithm (edge vertices)
open NumberedWindowRawExchangeVerticesTargets
open NumberedWindowRawExchangeVerticesExchangeTableProof (EarlierAgreement BoundAgreement)
open NumberedWindowRawExchangeVerticesTermStepProof (termStep)
open NumberedWindowRawExchangeVerticesArgsStepProof (argsStep)

/-- Strengthen only the internal simultaneous induction. Successful
raw exchange and the measure read the same raw getD defaults.
The final public theorem keeps the original syntax guard. -/
private theorem exchangeBound (hp : HeadPairs) (key : Nat) :
    ∀ a b, pair a b = key → BoundAgreement hp a b := by
  induction key using Nat.strongRecOn with
  | ind n ih =>
    intro a b k
    have before : EarlierAgreement hp a b := by
      intro x y h
      exact ih (pair x y) (k ▸ h) x y rfl
    exact ⟨termStep hp a b before,argsStep hp a b before⟩

theorem exactGuarded : ExactOriginalGuardedExchangeBounds := by
  intro hp a b
  have agrees := exchangeBound hp (pair a b) a b rfl
  constructor
  · intro h
    have pieces : (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true ∧ (row hp a b).1 = true := by
      simpa [bits,Bool.and_eq_true,and_assoc] using h
    exact agrees.1 pieces.2.2
  · intro h
    have pieces : (syntaxBits a).2 = true ∧ (syntaxBits b).2 = true ∧ (row hp a b).2 = true := by
      simpa [bits,Bool.and_eq_true,and_assoc] using h
    exact agrees.2 pieces.2.2

theorem exactVertices : ExactOriginalGuardedEdgeVertices := by
  intro s ctx requested a b checked
  have realEdge :
      (bits s.equivalentHeads a b).1 = true ∧
        NumberedWindowScalarAlgorithm.admitted s ctx requested a = true ∧
        NumberedWindowScalarAlgorithm.admitted s ctx requested b = true := by
    simpa [edge,Bool.and_eq_true,and_assoc] using checked
  have syntaxOk : (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true ∧
      (row s.equivalentHeads a b).1 = true := by
    simpa [bits,Bool.and_eq_true,and_assoc] using realEdge.1
  have same : (bounds a).1 = (bounds b).1 := (exactGuarded s.equivalentHeads a b).1 realEdge.1
  simp [vertices,cover,syntaxOk.1,syntaxOk.2.1,same]

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesVerticesProof
