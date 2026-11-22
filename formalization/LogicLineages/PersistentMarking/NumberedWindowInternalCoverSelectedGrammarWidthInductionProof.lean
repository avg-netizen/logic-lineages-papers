module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (widthInstance widthNext)
open NumberedWindowInternalCoverSelectedGrammarWidthBindingProof (consumeWidth)
open NumberedWindowInternalCoverSelectedGrammarWidthBaseProof (widthAtZero)
open NumberedWindowInternalCoverSelectedGrammarWidthStepProof (widthAtSuccessor)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem inductionAt (d H K m M : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF m (suc M)))) :
    Nonempty (Derivation body Γ (widthAt d H K m M)) := by
  let theta := widthMotive H K m M
  have base : Nonempty (Derivation body Γ (instantiate theta (emb z))) := by
    change Nonempty (Derivation body Γ (instantiate (widthMotive H K m M) (emb z)))
    rw [widthInstance]
    exact widthAtZero H K m M
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Δ := theta :: Γ.map weaken
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have bound' := renameInto bound j Δ keep
  rw [orderRename,sucRelabel] at bound'
  have ih : Nonempty (Derivation body Δ (widthAt x (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j))) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have step : Nonempty (Derivation body Δ (successorInstance theta)) := by
    change Nonempty (Derivation body Δ (successorInstance (widthMotive H K m M)))
    rw [widthNext]
    exact widthAtSuccessor x (H.relabel j) (K.relabel j) (m.relabel j) (M.relabel j) bound' ih
  obtain ⟨base⟩ := base
  obtain ⟨step⟩ := step
  have unrolled := Derivation.universalElimination (emb d) (natInduction theta base step)
  change Derivation body Γ (instantiate (widthMotive H K m M) (emb d)) at unrolled
  rw [widthInstance] at unrolled
  exact ⟨unrolled⟩

theorem exact_OpenSelectedGrammarWidth : ExactOpenSelectedGrammarWidth := by
  intro body α Γ d H K m M old oldTerms oldArgs next nextTerms nextArgs weak small large
  exact consumeWidth d H K m M old oldTerms oldArgs next nextTerms nextArgs
    (inductionAt d H K m M weak) small large

#print axioms exact_OpenSelectedGrammarWidth

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthInductionProof
