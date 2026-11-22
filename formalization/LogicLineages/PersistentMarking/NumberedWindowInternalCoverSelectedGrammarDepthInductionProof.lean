module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets
open NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof (adjacentInstance adjacentNext)
open NumberedWindowInternalCoverSelectedGrammarDepthBindingProof (consumeDepth)
open NumberedWindowInternalCoverSelectedGrammarDepthBaseProof (adjacentAtZero)
open NumberedWindowInternalCoverSelectedGrammarDepthStepProof (adjacentAtSuccessor)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem deriveAdjacent (d H K M : OTerm α) :
    Nonempty (Derivation body Γ (adjacentAt d H K M)) := by
  let theta := adjacentMotive H K M
  have base : Nonempty (Derivation body Γ (instantiate theta (emb z))) := by
    change Nonempty (Derivation body Γ (instantiate (adjacentMotive H K M) (emb z)))
    rw [adjacentInstance]
    exact adjacentAtZero H K M
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := theta :: Γ.map weaken
  have ih : Nonempty (Derivation body Δ (adjacentAt x (H.relabel j) (K.relabel j) (M.relabel j))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have step : Nonempty (Derivation body Δ (successorInstance theta)) := by
    change Nonempty (Derivation body Δ (successorInstance (adjacentMotive H K M)))
    rw [adjacentNext]
    exact adjacentAtSuccessor x (H.relabel j) (K.relabel j) (M.relabel j) ih
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := step
  have unrolled := Derivation.universalElimination (emb d) (natInduction theta base step)
  change Derivation body Γ (instantiate (adjacentMotive H K M) (emb d)) at unrolled
  rw [adjacentInstance] at unrolled
  exact ⟨unrolled⟩

theorem exact_OpenSelectedGrammarAdjacentDepth : ExactOpenSelectedGrammarAdjacentDepth := by
  intro body α Γ d H K M old oldTerms oldArgs next nextTerms nextArgs small large
  exact consumeDepth d (suc d) H K M old oldTerms oldArgs next nextTerms nextArgs
    (deriveAdjacent d H K M) small large

#print axioms exact_OpenSelectedGrammarAdjacentDepth

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthInductionProof
