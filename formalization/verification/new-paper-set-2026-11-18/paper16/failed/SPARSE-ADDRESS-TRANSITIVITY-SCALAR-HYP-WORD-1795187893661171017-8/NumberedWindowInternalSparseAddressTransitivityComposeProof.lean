module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityMiddleProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityBinderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityComposeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBackwardProof (backward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof
  (addressReportRename reportRename dataRename reportsCases supply)
open NumberedWindowInternalSparseAddressPositiveOpenSideProof (align)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveTransitivityChecks (exact_OpenPositiveTransitivity)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedCases)
open NumberedWindowInternalSparseAddressTransitivityBinderProof (provide suppliedEdgeRename)
open NumberedWindowInternalSparseAddressTransitivityMiddleProof (joinMiddle movePositive)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem closeNew (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left right c t src dst : OTerm α)
    (leftRep : Nonempty (Derivation body Γ (addressReport left c t src)))
    (rightRep : Nonempty (Derivation body Γ (addressReport right c t dst)))
    (vc : Nonempty (Derivation body Γ (unary cv (suc z) c)))
    (vt : Nonempty (Derivation body Γ (unary tv (suc z) t)))
    (path : Nonempty (Derivation body Γ
      (NumberedWindowInternalSparsePositiveTransitivityTargets.supplied raw least c t src dst))) :
    Nonempty (Derivation body Γ (suppliedEdge (addressPositive cv tv raw least) left right)) := by
  let r := addressPositive cv tv raw least
  apply suppliedCases raw least c t src dst (suppliedEdge r left right) path
  intro β j Δ cert hJ p
  rw [suppliedEdgeRename]
  have l := renameInto leftRep j Δ hJ
  have rr := renameInto rightRep j Δ hJ
  have cc := renameInto vc j Δ hJ
  have tt := renameInto vt j Δ hJ
  rw [addressReportRename] at l rr
  simp only [unaryRename,sucRelabel,zRelabel] at cc tt
  obtain ⟨l⟩ := l
  obtain ⟨rr⟩ := rr
  obtain ⟨cc⟩ := cc
  obtain ⟨tt⟩ := tt
  obtain ⟨p⟩ := p
  let a := left.relabel j
  let b := right.relabel j
  have row : Nonempty (Derivation body Δ
      (witnessData cv tv raw least a cert b (c.relabel j) (t.relabel j) (src.relabel j) (dst.relabel j))) :=
    ⟨Derivation.conjunctionIntroduction l (Derivation.conjunctionIntroduction rr
      (Derivation.conjunctionIntroduction cc (Derivation.conjunctionIntroduction tt p)))⟩
  exact provide r a cert b (backward cv tv raw least a cert b
    (supply cv tv raw least a cert b (c.relabel j) (t.relabel j) (src.relabel j) (dst.relabel j) row))

theorem fromReports (cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left first mid second right c₁ t₁ src m₁ c₂ t₂ m₂ dst : OTerm α)
    (firstRep : Nonempty (Derivation body Γ
      (witnessData cv tv raw least left first mid c₁ t₁ src m₁)))
    (secondRep : Nonempty (Derivation body Γ
      (witnessData cv tv raw least mid second right c₂ t₂ m₂ dst))) :
    Nonempty (Derivation body Γ (suppliedEdge (addressPositive cv tv raw least) left right)) := by
  obtain ⟨a⟩ := firstRep
  obtain ⟨b⟩ := secondRep
  let firstRest := Derivation.conjunctionRight a
  let firstValid := Derivation.conjunctionRight firstRest
  let secondRest := Derivation.conjunctionRight b
  let secondValid := Derivation.conjunctionRight secondRest
  obtain ⟨hc,ht,hk⟩ := joinMiddle mid c₁ t₁ m₁ c₂ t₂ m₂
    ⟨Derivation.conjunctionLeft firstRest⟩ ⟨Derivation.conjunctionLeft b⟩
  have rightRep := align right c₂ t₂ c₁ t₁ dst hc ht ⟨Derivation.conjunctionLeft secondRest⟩
  have secondPath : Nonempty (Derivation body Γ (positiveAt raw least c₁ t₁ m₁ second dst)) :=
    movePositive raw least c₁ t₁ m₁ c₂ t₂ m₂ second dst hc ht hk
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight secondValid)⟩
  obtain ⟨next⟩ := secondPath
  have both : Nonempty (Derivation body Γ
    (positiveAt raw least c₁ t₁ src first m₁ ⊓ positiveAt raw least c₁ t₁ m₁ second dst)) :=
    ⟨Derivation.conjunctionIntroduction
      (Derivation.conjunctionRight (Derivation.conjunctionRight firstValid)) next⟩
  have composed := closedApply (exact_OpenPositiveTransitivity body raw least α c₁ t₁ src first m₁ second dst) both
  exact closeNew cv tv raw least left right c₁ t₁ src dst ⟨Derivation.conjunctionLeft a⟩ rightRep
    ⟨Derivation.conjunctionLeft firstValid⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight firstValid)⟩ composed

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityComposeProof
