module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumOpenStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalControlGraphSupportProof (valueUnique projectionValue successorValue compositionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseDecodeSyntaxProof (binary binaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseOrderedMinimum
open NumberedWindowInternalSparseOrderedMinimumTargets

attribute [local irreducible] programGraph

theorem disjRename {α β : Type} (A B : Formula α) (j : α → β) :
    (A ⊔ B).relabel j = A.relabel j ⊔ B.relabel j := rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- This internal case split uses the actual control program at the same
tape. No assumption about the comparison's external numeric behavior. -/
private theorem selectedSide (control no yes : Program 2) (out h prior : OTerm α)
    (selected : Nonempty (Derivation body Γ (binary (branch control no yes) out h prior))) :
    Nonempty (Derivation body Γ (binary no out h prior ⊔ binary yes out h prior)) := by
  apply optionGraphCases control ![h,prior] _
  · intro β j Δ keep hv
    simp only [disjRename,binaryRename]
    rw [binaryInputsRename] at hv
    have actual := renameInto selected j Δ keep
    rw [binaryRename] at actual
    obtain ⟨zero⟩ := zeroBranchElim control no yes (out.relabel j) ![h.relabel j,prior.relabel j] hv actual
    exact ⟨orLeft zero⟩
  · intro β j Δ p keep hv
    simp only [disjRename,binaryRename]
    rw [binaryInputsRename] at hv
    have actual := renameInto selected j Δ keep
    rw [binaryRename] at actual
    obtain ⟨positive⟩ := successorBranchElim control no yes (out.relabel j) p ![h.relabel j,prior.relabel j] hv actual
    exact ⟨orRight positive⟩

private theorem offerValue (h prior : OTerm α) :
    Nonempty (Derivation body Γ (binary offerHead (suc h) h prior)) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2)) (suc h) ![h,prior] ![h]
    (successorValue ![h])
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![h,prior]

private theorem fromOffer (h prior k : OTerm α) :
    Nonempty (Derivation body Γ ((binary offerHead (suc k) h prior).imp (eqn k h ⊔ eqn prior (suc k)))) := by
  let premise := binary offerHead (suc k) h prior
  obtain ⟨same⟩ := valueUnique (body := body) (Gamma := premise :: Γ) offerHead (suc k) (suc h) ![h,prior]
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (offerValue h prior)
  exact ⟨Derivation.implicationIntroduction (orLeft (cancelSuc same))⟩

private theorem fromPrior (h prior k : OTerm α) :
    Nonempty (Derivation body Γ ((binary (.projection 1) (suc k) h prior).imp (eqn k h ⊔ eqn prior (suc k)))) := by
  let premise := binary (.projection 1) (suc k) h prior
  obtain ⟨same⟩ := valueUnique (body := body) (Gamma := premise :: Γ) (.projection (1 : Fin 2))
    prior (suc k) ![h,prior] (projectionValue 1 ![h,prior]) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (orRight same)⟩

theorem pick (h prior k : OTerm α)
    (accepted : Nonempty (Derivation body Γ (binary minimumStep (suc k) h prior))) :
    Nonempty (Derivation body Γ (eqn k h ⊔ eqn prior (suc k))) := by
  let later := branch preferHead (.projection (1 : Fin 2)) offerHead
  let premise := binary later (suc k) h prior
  obtain ⟨outer⟩ := selectedSide (.projection (1 : Fin 2)) offerHead later (suc k) h prior accepted
  obtain ⟨headCase⟩ := fromOffer (body := body) (Γ := Γ) h prior k
  obtain ⟨inner⟩ := selectedSide (body := body) (Γ := premise :: Γ) preferHead
    (.projection (1 : Fin 2)) offerHead (suc k) h prior ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨priorCase⟩ := fromPrior (body := body) (Γ := premise :: Γ) h prior k
  obtain ⟨offerCase⟩ := fromOffer (body := body) (Γ := premise :: Γ) h prior k
  have next := Derivation.implicationIntroduction (disjunctionElimination inner priorCase offerCase)
  exact ⟨disjunctionElimination outer headCase next⟩

theorem stepOpen : ExactOpenOrderedMinimumStep := by
  intro body α Γ h prior k
  let premise := binary minimumStep (suc k) h prior
  obtain ⟨selected⟩ := pick (body := body) (Γ := premise :: Γ) h prior k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction selected⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumOpenStepProof
