module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterPayloadProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalControlGraphSupportProof
  (programRename successorValue valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply cancelSuc symm)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalFreshProbeEmitter
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def positiveArm (p : Selectors) : Program 1 :=
  .composition .succ (Fin.cons (emitSelected p) Fin.elim0)

private theorem fromSuccessor (p : Selectors) (q u : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (positiveArm p) (suc u) ![q]))) :
    Nonempty (Derivation body Γ (programGraph (emitSelected p) u ![q])) := by
  apply programCompositionCases Program.succ (Fin.cons (emitSelected p) Fin.elim0)
    (suc u) ![q] (programGraph (emitSelected p) u ![q]) h
  intro β j ys Δ _ hf hg
  rw [programRename,unaryRename]
  rw [sucRelabel] at hf
  obtain ⟨he⟩ := valueUnique Program.succ (suc (u.relabel j)) (suc (ys 0)) ys hf (successorValue ys)
  have hx := hg 0
  rw [unaryRename] at hx
  exact outputTransport (emitSelected p) (ys 0) (u.relabel j) ![q.relabel j]
    ⟨symm (cancelSuc he)⟩ hx

/-- Remove the actual output successor by PA injectivity. The branch
decision is a genuine case split on the actual guard graph (and not a
test of the standard interpretation of the open source term). -/
theorem actualPayload (p : Selectors) (q u : OTerm α)
    (h : Nonempty (Derivation body Γ (freshAt (chooseFresh p) q u))) :
    Nonempty (Derivation body Γ (programGraph (emitSelected p) u ![q])) := by
  change Nonempty (Derivation body Γ (programGraph (chooseFresh p) (suc u) ![q])) at h
  unfold chooseFresh at h
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.1] at h
  change Nonempty (Derivation body Γ
    (programGraph (branch p.good (constantZero 1) (positiveArm p)) (suc u) ![q])) at h
  apply optionGraphCases p.good ![q] (programGraph (emitSelected p) u ![q])
  · intro β j Δ hj hz
    have hp := renameInto h j Δ hj
    rw [programRename,unaryRename,sucRelabel] at hp
    rw [unaryRename] at hz
    have hBad := zeroBranchElim p.good (constantZero 1) (positiveArm p)
      (suc (u.relabel j)) ![q.relabel j] hz hp
    obtain ⟨he⟩ := valueUnique (constantZero 1) (suc (u.relabel j)) z ![q.relabel j]
      hBad (constantZeroValue ![q.relabel j])
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
  · intro β j Δ k hj hs
    have hp := renameInto h j Δ hj
    rw [programRename,unaryRename,sucRelabel] at hp
    rw [unaryRename] at hs
    rw [programRename,unaryRename]
    exact fromSuccessor p (q.relabel j) (u.relabel j)
      (successorBranchElim p.good (constantZero 1) (positiveArm p)
        (suc (u.relabel j)) k ![q.relabel j] hs hp)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterPayloadProof
