module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterGuardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof
  (programRename outputTransport valueUnique equalEqn)
open ID1Completion.InternalControlGraphProof (actualOriginalEqualsOneGraph)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases oneTuple)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalQuotientComparisonProof (disjunctionElimination)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeEmitter (chooseFresh emitSelected)
open NumberedWindowInternalFreshProbeParsedEmitter

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem equalsOneSuccess (v t : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph equalsOne (suc t) ![v]))) :
    Nonempty (Derivation body Γ (eqn (suc t) (suc z))) := by
  obtain ⟨rule⟩ := actualOriginalEqualsOneGraph body α (suc t) v
  obtain ⟨cause⟩ := h
  have d := Derivation.implicationElimination (weakenClosed (Derivation.conjunctionLeft rule) Γ) cause
  change Derivation body Γ ((equal v (suc z) ⊓ equal (suc t) (suc z)) ⊔
    ((equal v (suc z)).not ⊓ equal (suc t) z)) at d
  simp only [equalEqn] at d
  exact ⟨disjunctionElimination d
    (Derivation.implicationIntroduction (Derivation.conjunctionRight
      (Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (Derivation.explosion
      (sucNeZeroApply (Derivation.conjunctionRight
        (Derivation.hypothesis List.mem_cons_self)))))⟩

/-- This is the original ID1 equals-one graph, not normalization in a
different registry calculus or an external Boolean-valued assumption. -/
private theorem normalizedSuccess (p : Program 1) (q t : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (normalize p) (suc t) ![q]))) :
    Nonempty (Derivation body Γ (programGraph (normalize p) (suc z) ![q])) := by
  have ee : Nonempty (Derivation body Γ (eqn (suc t) (suc z))) := by
    apply programCompositionCases equalsOne (fun _ : Fin 1 => p) (suc t) ![q] _ h
    intro β j ys Δ _ hf _
    simp only [ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel,zRelabel]
    rw [sucRelabel,← oneTuple ys] at hf
    exact equalsOneSuccess (ys 0) (t.relabel j) hf
  exact outputTransport (normalize p) (suc t) (suc z) ![q] ee h

private def positiveArm (scalarProg bound : Program 1) : Program 1 :=
  .composition .succ (Fin.cons (emitSelected (selected scalarProg bound)) Fin.elim0)

theorem checkedGuard (scalarProg bound : Program 1) (q u : OTerm α)
    (h : Nonempty (Derivation body Γ (freshAt (chooseFresh (selected scalarProg bound)) q u))) :
    Nonempty (Derivation body Γ (programGraph (selectedGuard scalarProg) (suc z) ![q])) := by
  change Nonempty (Derivation body Γ
    (programGraph (chooseFresh (selected scalarProg bound)) (suc u) ![q])) at h
  unfold chooseFresh at h
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.1] at h
  change Nonempty (Derivation body Γ (programGraph
    (branch (selectedGuard scalarProg) (constantZero 1) (positiveArm scalarProg bound)) (suc u) ![q])) at h
  apply optionGraphCases (selectedGuard scalarProg) ![q] _
  · intro β j Δ hj h0
    have moved := renameInto h j Δ hj
    rw [programRename,unaryRename,sucRelabel] at moved
    rw [unaryRename] at h0
    have bad := zeroBranchElim (selectedGuard scalarProg) (constantZero 1)
      (positiveArm scalarProg bound) (suc (u.relabel j)) ![q.relabel j] h0 moved
    obtain ⟨absurdEq⟩ := valueUnique (constantZero 1) (suc (u.relabel j)) z ![q.relabel j]
      bad (constantZeroValue ![q.relabel j])
    exact ⟨Derivation.explosion (sucNeZeroApply absurdEq)⟩
  · intro β j Δ t _ ht
    simp only [programRename,unaryRename,sucRelabel,zRelabel]
    rw [unaryRename] at ht
    exact normalizedSuccess _ (q.relabel j) t ht

theorem guardReports (scalarProg : Program 1) (q : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (selectedGuard scalarProg) (suc z) ![q]))) :
    Nonempty (Derivation body Γ (programGraph addressGood (suc z) ![q])) ∧
    Nonempty (Derivation body Γ (programGraph arrowGood (suc z) ![q])) := by
  unfold selectedGuard at h
  obtain ⟨main⟩ := normalizeRecover _ ![q] h
  rw [exact_DispatchControlAST.2.2.2.2.2] at main
  obtain ⟨row⟩ := conjunctionRecover scalarProg parserGuard ![q] ⟨main⟩
  have hp := Derivation.conjunctionRight row
  unfold parserGuard at hp
  rw [exact_DispatchControlAST.2.2.2.2.2] at hp
  obtain ⟨h⟩ := conjunctionRecover addressGood arrowGood ![q] ⟨hp⟩
  exact ⟨⟨Derivation.conjunctionLeft h⟩,⟨Derivation.conjunctionRight h⟩⟩

theorem gatePreserves (scalarProg datum : Program 1) (q x : OTerm α)
    (guard : Nonempty (Derivation body Γ (programGraph (selectedGuard scalarProg) (suc z) ![q])))
    (rawValue : Nonempty (Derivation body Γ (programGraph datum x ![q]))) :
    Nonempty (Derivation body Γ (programGraph (gated (selectedGuard scalarProg) datum) x ![q])) := by
  unfold gated
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.1]
  exact successorBranchIntro (selectedGuard scalarProg) (constantZero 1) datum x z ![q] guard rawValue

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterGuardProof
