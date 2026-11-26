module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open NumberedWindowInternalCoverSelectedGrammarDepthBindingProof (consumeDepth)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
open NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof (upperInstance upperNext)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthBindingProof (useLower)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthStepProof (lowerAtZero lowerAtSuccessor)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem allDepthsAt (D H K M : OTerm α) :
    Nonempty (Derivation body Γ (allLower D H K M)) := by
  let theta := upperMotive H K M
  have base : Nonempty (Derivation body Γ (instantiate theta (emb z))) := by
    change Nonempty (Derivation body Γ (instantiate (upperMotive H K M) (emb z)))
    rw [upperInstance]
    exact lowerAtZero H K M
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := theta :: Γ.map weaken
  have ih : Nonempty (Derivation body Δ (allLower x (H.relabel j) (K.relabel j) (M.relabel j))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have step : Nonempty (Derivation body Δ (successorInstance theta)) := by
    change Nonempty (Derivation body Δ (successorInstance (upperMotive H K M)))
    rw [upperNext]
    exact lowerAtSuccessor x (H.relabel j) (K.relabel j) (M.relabel j) ih
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := step
  have h := Derivation.universalElimination (emb D) (natInduction theta base step)
  change Derivation body Γ (instantiate (upperMotive H K M) (emb D)) at h
  rw [upperInstance] at h
  exact ⟨h⟩

theorem exact_OpenSelectedGrammarWeakDepth : ExactOpenSelectedGrammarWeakDepth := by
  intro body α Γ d D H K M old oldTerms oldArgs next nextTerms nextArgs weak small large
  have one := useLower d D H K M (allDepthsAt D H K M) weak
  exact consumeDepth d D H K M old oldTerms oldArgs next nextTerms nextArgs one small large

#print axioms exact_OpenSelectedGrammarWeakDepth

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthInductionProof
