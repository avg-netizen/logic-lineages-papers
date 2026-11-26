module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenGateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (hopGood hopTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathAdvance
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev continued (raw : Program 5) (least : Program 3) :=
  conjunction (atHop hopGood) (conjunction (rawCall raw) (conjunction (fromMatches least) (toMatches least)))

private theorem fromTarget (c ty s h t : OTerm α)
    (hOut : Nonempty (Derivation body Γ (programGraph targetCode (suc t) (coords c ty s h)))) :
    Nonempty (Derivation body Γ (selectedTarget t c ty s h)) := by
  apply programCases (atHop hopTarget) (coords c ty s h) _
  intro β j Δ v hJ actual
  change Nonempty (Derivation body Δ
    ((programGraph (atHop hopTarget) t (coords c ty s h)).relabel j))
  rw [quadRename]
  rw [coordsRename] at actual
  let c' := c.relabel j
  let ty' := ty.relabel j
  let s' := s.relabel j
  let h' := h.relabel j
  have out := moveQuad j Δ hJ targetCode (suc t) c ty s h hOut
  rw [sucRelabel] at out
  obtain ⟨eq⟩ := valueUnique targetCode (suc v) (suc (t.relabel j)) (coords c' ty' s' h')
    (targetGraph v c' ty' s' h' actual) out
  exact outputTransport (atHop hopTarget) v (t.relabel j) (coords c' ty' s' h')
    ⟨cancelSuc eq⟩ actual

theorem resultOfGate (raw : Program 5) (least : Program 3) (c ty s h t : OTerm α)
    (ok : Nonempty (Derivation body Γ (acceptedGuard raw least c ty s h)))
    (called : Nonempty (Derivation body Γ (selectedTarget t c ty s h))) :
    Nonempty (Derivation body Γ (selectedGraph raw least (suc t) c ty s h)) :=
  successorBranchIntro (advanceGood raw least) (constantZero 4) targetCode (suc t) z
    (coords c ty s h) ok (targetGraph t c ty s h called)

private theorem resultZero (raw : Program 5) (least : Program 3) (c ty s h : OTerm α)
    (bad : Nonempty (Derivation body Γ (programGraph (advanceGood raw least) z (coords c ty s h)))) :
    Nonempty (Derivation body Γ (selectedGraph raw least z c ty s h)) :=
  zeroBranchIntro (advanceGood raw least) (constantZero 4) targetCode z
    (coords c ty s h) bad (zeroConstantValue (coords c ty s h))

private theorem verifyGuard (raw : Program 5) (least : Program 3) (c ty s h t : OTerm α)
    (out : Nonempty (Derivation body Γ (selectedGraph raw least (suc t) c ty s h))) :
    Nonempty (Derivation body Γ (acceptedGuard raw least c ty s h)) := by
  obtain ⟨out⟩ := out
  let P := acceptedGuard raw least c ty s h
  have yes : Derivation body (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  have no : Nonempty (Derivation body (P.not :: Γ) P) := by
    have noGuard : Nonempty (Derivation body (P.not :: Γ)
      (programGraph (advanceGood raw least) z (coords c ty s h))) :=
      conjunctionReject statePresent (continued raw least) (coords c ty s h)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero := resultZero raw least c ty s h noGuard
    obtain ⟨eq⟩ := valueUnique (advance raw least) (suc t) z (coords c ty s h)
      ⟨addHyp out P.not⟩ zero
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle P) (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction no)⟩

theorem recoverGate (raw : Program 5) (least : Program 3) (c ty s h t : OTerm α)
    (out : Nonempty (Derivation body Γ (selectedGraph raw least (suc t) c ty s h))) :
    Nonempty (Derivation body Γ (acceptedGuard raw least c ty s h ⊓ selectedTarget t c ty s h)) := by
  have ok := verifyGuard raw least c ty s h t out
  have picked := successorBranchElim (advanceGood raw least) (constantZero 4) targetCode
    (suc t) z (coords c ty s h) ok out
  obtain ⟨hp⟩ := fromTarget c ty s h t picked
  obtain ⟨hg⟩ := ok
  exact ⟨Derivation.conjunctionIntroduction hg hp⟩

theorem gate : OpenAdvanceGate := by
  intro body raw least α c ty s h t
  let a := acceptedGuard raw least c ty s h ⊓ selectedTarget t c ty s h
  let b := selectedGraph raw least (suc t) c ty s h
  have lhs : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have rhs : Derivation body [b] b := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := resultOfGate raw least c ty s h t
    ⟨Derivation.conjunctionLeft lhs⟩ ⟨Derivation.conjunctionRight lhs⟩
  obtain ⟨backward⟩ := recoverGate raw least c ty s h t ⟨rhs⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem empty : OpenNoCurrent := by
  intro body raw least α c ty h
  let P := acceptedGuard raw least c ty z h
  have no : Nonempty (Derivation body [] P.not) := by
    obtain ⟨yes⟩ := conjunctionRecover (body := body) (Gamma := [P])
      statePresent (continued raw least) (coords c ty z h)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨eq⟩ := valueUnique statePresent (suc z) z (coords c ty z h)
      ⟨Derivation.conjunctionLeft yes⟩ (stateZero c ty h)
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply eq)⟩
  exact resultZero raw least c ty z h
    (conjunctionReject statePresent (continued raw least) (coords c ty z h) no)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenGateProof
