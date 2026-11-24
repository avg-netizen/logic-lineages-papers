module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenBodyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFrameOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique programRename)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanProof (lessOfAcceptance)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (eqn emb eqnSubst bindEmbedding liftBind varBind sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenBodyProof (readPackedBody)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralBoundedFallback
open NumberedWindowInternalLiteralOrderedSelectorsProof (D selectorCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem pairInputsRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem sucEq (a b : OTerm α) (h : D B Γ (eqn a b)) : D B Γ (eqn (suc a) (suc b)) := by
  let theta : Formula (α ⊕ Fin 1) := eqn (suc (a.relabel Sum.inl)) (suc (.var (.inr 0)))
  have inst (v : OTerm α) : instantiate theta (emb v) = eqn (suc a) (suc v) := by
    simp only [theta,instantiate,eqnSubst,bindEmbedding,liftBind,varBind,
      ID1Completion.InternalTagArithmeticSyntaxProof.sucSubst]
  obtain ⟨e⟩ := h
  have atA : Derivation B Γ (instantiate theta (emb a)) := by rw [inst]; exact refl _
  have d := Derivation.equalityElimination theta (emb a) (emb b) e atA
  rw [inst] at d
  exact ⟨d⟩

theorem atLeft (p : Program 1) (out a b : OTerm α)
    (h : D B Γ (unary p out a)) : D B Γ (programGraph (atCandidate p) out ![a,b]) := by
  apply compositionValue p ![.projection 0] out ![a,b] ![a] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![a,b]

private theorem leftUnary (p : Program 1) (out a b : OTerm α)
    (h : D B Γ (programGraph (atCandidate p) out ![a,b])) : D B Γ (unary p out a) := by
  apply compositionRecover p ![.projection 0] out ![a,b] ![a] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![a,b]

private theorem checkDescent (a b w : OTerm α)
    (selectChild : D B Γ (unary childSelector w a))
    (accept : D B Γ (programGraph descends (suc z) ![a,b])) : D B Γ (ltF w b) := by
  apply lessOfAcceptance
  apply compositionRecover ltTest ![atCandidate childSelector,.projection 1] (suc z)
    ![a,b] ![w,b] accept
  intro i
  exact Fin.cases (atLeft childSelector w a b selectChild)
    (Fin.cases (projectionValue 1 ![a,b]) (fun k => Fin.elim0 k)) i

/-- From actual acceptance of the bounded observer at a positive code,
recover an exact ordered child frame and the original object strict
order of its actual witness, independently of callback calibration. -/
theorem exact_OpenBoundedFrameParts (base parent : OTerm α) (goal : Formula α)
    (yes : D B Γ (programGraph admitted (suc z) ![suc base,parent]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (q w r : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (suc (base.relabel j)) (frameValueTerm q w r)) →
      D B Δ (ltF w (parent.relabel j)) → D B Δ (goal.relabel j)) : D B Γ goal := by
  apply selectorCases B 3 α Γ (suc base) predOne goal
  intro β j Δ values keep len reports
  rcases values with _ | ⟨q,_ | ⟨w,_ | ⟨r,_ | ⟨a,rest⟩⟩⟩⟩ <;> simp at len
  let v := base.relabel j
  let u := parent.relabel j
  let c := suc v
  have moved := renameInto yes j Δ keep
  rw [programRename,pairInputsRename,sucRelabel,zRelabel,sucRelabel] at moved
  have data := conjunctionRecover (atCandidate frameShape) descends ![c,u] moved
  obtain ⟨d⟩ := data
  have arity := leftUnary frameShape (suc z) c u ⟨Derivation.conjunctionLeft d⟩
  have reps : Reports B Δ c predOne [q,w,r] := by simpa only [sucRelabel] using reports
  have found := readPackedBody B 3 β Δ c predOne [q,w,r] rfl arity reps
  have exactPred : D B Δ (unary predOne v c) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor v
  have eq := valueUnique predOne v (packedBody [q,w,r]) ![c] exactPred found
  have same : D B Δ (eqn c (frameValueTerm q w r)) := sucEq _ _ eq
  have smaller := checkDescent c u w reps.2.1 ⟨Derivation.conjunctionRight d⟩
  exact use β j Δ q w r keep same smaller

#print axioms exact_OpenBoundedFrameParts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFrameOpenProof
