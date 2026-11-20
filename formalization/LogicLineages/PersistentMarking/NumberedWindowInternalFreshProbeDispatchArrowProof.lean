module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectGraphProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchArrowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (constantZero branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionRecover)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalProbeTargets (OTerm typeCode freshAt typedAt witnesses)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchObjectTargets
open NumberedWindowInternalFreshProbeDispatchObjectGraphProof (memberAt dispatchReject)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (binaryRename witnessesRename witnessesIntro)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Acceptance of the actual zero-rejecting branch gives an object
successor payload and the actual nonzero-branch graph, with its original
arguments. The zero case contradicts the reported output one. -/
private theorem acceptingBranchCases {n : Nat} (control other : Program n)
    (xs : Fin n → OTerm α) (ψ : Formula α)
    (h : Nonempty (Derivation body Γ
      (programGraph (chooseBranch control (zeroAt n) other) (numeral 1) xs)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph control (suc u) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Δ (programGraph other (numeral 1) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Δ (ψ.relabel j))) :
    Nonempty (Derivation body Γ ψ) := by
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.1] at h
  apply optionGraphCases control xs ψ
  · intro β j Δ hj hz
    let ys : Fin n → OTerm β := fun i => (xs i).relabel j
    have hp := renameInto h j Δ hj
    rw [programRename,numeralRename] at hp
    have hBad := zeroBranchElim control (constantZero n) other (numeral 1) ys hz hp
    obtain ⟨he⟩ := valueUnique (constantZero n) (numeral 1) z ys hBad (constantZeroValue ys)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
  · intro β j Δ u hj hs
    have hp := renameInto h j Δ hj
    rw [programRename,numeralRename] at hp
    exact k β j Δ u hj hs (successorBranchElim control (constantZero n) other (numeral 1) u
      (fun i => (xs i).relabel j) hs hp)

private theorem predecessorAt {n : Nat} (a : Program n) (xs : Fin n → OTerm α) (u : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph a (suc u) xs))) :
    Nonempty (Derivation body Γ (programGraph (afterPredecessor a) u xs)) := by
  have hp : Nonempty (Derivation body Γ (programGraph predOne u ![suc u])) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor u
  unfold afterPredecessor
  apply compositionValue predOne _ u xs ![suc u] hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact h

private abbrev afterFresh (l : Leaves) (k : Program 1) : Program 1 :=
  .composition (applicationPart l k)
    (Fin.cons (Program.projection (0 : Fin 1)) (Fin.cons (afterPredecessor l.fresh) Fin.elim0))

private abbrev afterApplication (l : Leaves) (k : Program 1) : Program 2 :=
  .composition (resultGuard l k)
    (Fin.cons (Program.projection (0 : Fin 2))
      (Fin.cons (Program.projection (1 : Fin 2)) (Fin.cons (afterPredecessor l.applicationCode) Fin.elim0)))

private theorem recoverApplication (l : Leaves) (k : Program 1) (q u : OTerm α)
    (hf : Nonempty (Derivation body Γ (programGraph l.fresh (suc u) ![q])))
    (h : Nonempty (Derivation body Γ (programGraph (afterFresh l k) (numeral 1) ![q]))) :
    Nonempty (Derivation body Γ (programGraph (applicationPart l k) (numeral 1) ![q,u])) := by
  apply compositionRecover (applicationPart l k)
    (Fin.cons (Program.projection (0 : Fin 1)) (Fin.cons (afterPredecessor l.fresh) Fin.elim0))
    (numeral 1) ![q] ![q,u] h
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · exact projectionValue (0 : Fin 1) ![q]
  · exact predecessorAt l.fresh ![q] u hf

private theorem recoverResult (l : Leaves) (k : Program 1) (q u v : OTerm α)
    (ha : Nonempty (Derivation body Γ (programGraph l.applicationCode (suc v) ![q,u])))
    (h : Nonempty (Derivation body Γ (programGraph (afterApplication l k) (numeral 1) ![q,u]))) :
    Nonempty (Derivation body Γ (programGraph (resultGuard l k) (numeral 1) ![q,u,v])) := by
  apply compositionRecover (resultGuard l k)
    (Fin.cons (Program.projection (0 : Fin 2))
      (Fin.cons (Program.projection (1 : Fin 2)) (Fin.cons (afterPredecessor l.applicationCode) Fin.elim0)))
    (numeral 1) ![q,u] ![q,u,v] h
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · exact projectionValue (0 : Fin 2) ![q,u]
  · exact projectionValue (1 : Fin 2) ![q,u]
  · exact predecessorAt l.applicationCode ![q,u] v ha

private theorem recoverFactors (l : Leaves) (k : Program 1) (q u v : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (resultGuard l k) (numeral 1) ![q,u,v]))) :
    Nonempty (Derivation body Γ (accepts l.applicationGuard q u v)) ∧
      Nonempty (Derivation body Γ (programGraph k (numeral 1) ![v])) := by
  unfold resultGuard at h
  rw [exact_DispatchControlAST.2.2.2.2.2] at h
  obtain ⟨hs⟩ := conjunctionRecover l.applicationGuard
    (.composition k (Fin.cons (Program.projection (2 : Fin 3)) Fin.elim0)) ![q,u,v] h
  refine ⟨⟨Derivation.conjunctionLeft hs⟩,?_⟩
  apply compositionRecover k (Fin.cons (Program.projection (2 : Fin 3)) Fin.elim0)
    (numeral 1) ![q,u,v] ![v] ⟨Derivation.conjunctionRight hs⟩
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) ![q,u,v]

theorem arrowBranch : ExactProbeArrowBranch := by
  intro l W σ τ hm body α Γ q h
  change Nonempty (Derivation body Γ (programGraph
    (bothOne (typeLeaf l (.arrow σ τ)) (arrowPart l (verify l τ))) (numeral 1) ![q])) at h
  rw [exact_DispatchControlAST.2.2.2.2.2] at h
  obtain ⟨hs⟩ := conjunctionRecover (typeLeaf l (.arrow σ τ)) (arrowPart l (verify l τ)) ![q] h
  have hArrow : Nonempty (Derivation body Γ (programGraph
      (chooseBranch l.fresh (zeroAt 1) (afterFresh l (verify l τ))) (numeral 1) ![q])) :=
    ⟨Derivation.conjunctionRight hs⟩
  apply acceptingBranchCases l.fresh (afterFresh l (verify l τ)) ![q]
    (witnesses l.applicationGuard (dispatch l W) l.fresh τ q) hArrow
  intro β j Δ u _ hf hAfter
  rw [witnessesRename]
  rw [unaryRename] at hf hAfter
  let q' := q.relabel j
  have hApp : Nonempty (Derivation body Δ (programGraph
      (chooseBranch l.applicationCode (zeroAt 2) (afterApplication l (verify l τ)))
      (numeral 1) ![q',u])) := recoverApplication l (verify l τ) q' u hf hAfter
  apply acceptingBranchCases l.applicationCode (afterApplication l (verify l τ)) ![q',u]
    (witnesses l.applicationGuard (dispatch l W) l.fresh τ q') hApp
  intro γ k Θ v hk ha hResult
  rw [witnessesRename]
  rw [binaryRename] at ha hResult
  have hf' := renameInto hf k Θ hk
  rw [programRename,sucRelabel,unaryRename] at hf'
  have hFacts := recoverFactors l (verify l τ) (q'.relabel k) (u.relabel k) v
    (recoverResult l (verify l τ) (q'.relabel k) (u.relabel k) v ha hResult)
  have hTyped : Nonempty (Derivation body Θ (typedAt (dispatch l W) τ v)) :=
    (memberAt l W τ hm (numeral 1) v).mpr hFacts.2
  exact witnessesIntro l.applicationGuard (dispatch l W) l.fresh τ
    (q'.relabel k) (u.relabel k) v hf' hFacts.1 hTyped

theorem typedTotal : ExactProbeTypedTotal := by
  intro l W closed d c σ τ α Γ q ht
  by_cases hm : LogicLineages.OrdinalComparison.Source.Ty.arrow σ τ ∈ W
  · exact arrowBranch l W σ τ (closed σ τ hm) _ α Γ q
      ((memberAt l W (.arrow σ τ) hm (numeral 1) q).mp ht)
  · have hz := dispatchReject l W (.arrow σ τ) hm
      (ID1Completion.SourcePresentation.sourceBody d c) α Γ q
    obtain ⟨he⟩ := valueUnique (dispatch l W) (numeral 1) z
      ![numeral (typeCode (.arrow σ τ)),q] ht hz
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchArrowProof
