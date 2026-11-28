module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureTargetsV2
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationDomainProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

/-! Proofs of the frozen `OriginalWindowDomain` and `OpenLiteralFiniteDomain`
(`Paper16AccessibilityMilestoneDomainClosureTargetsV2`; Fable B2, 27 November 2026). The numeric
half mirrors `exact_OriginalWindowChild` with `arrowLeft`; the open half mirrors
`exact_OpenLiteralFiniteCodomain` with the head selector of the cell. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowProbeCode (code)
open NumberedWindowApplicationDomainProof (arrowLeft subtypeSelf)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypeMembershipProof (exact_FiniteProgramImageTransfer)
open Paper16AccessibilityMilestoneDomainClosureTargetsV2

theorem exact_OriginalWindowDomain : OriginalWindowDomain := by
  intro K hk σ τ h
  obtain ⟨ρ, hρ, he⟩ := List.mem_map.mp h
  cases ρ with
  | ground => cases he
  | arrow a b =>
    change LogicLineages.OrdinalComparison.Source.Ty.arrow (formulaType a) (formulaType b) =
      LogicLineages.OrdinalComparison.Source.Ty.arrow σ τ at he
    have ha : formulaType a = σ := (LogicLineages.OrdinalComparison.Source.Ty.arrow.inj he).1
    exact List.mem_map.mpr ⟨a, arrowLeft hk hρ a (subtypeSelf a), ha⟩

private theorem headOfCodes (P : List ProbeTy) (closed : DomainClosed P) (t : Nat)
    (mem : t ∈ finiteCodes P) : evaluate cellHead (t ::ᵥ nil) ∈ finiteCodes P := by
  obtain ⟨p, inP, rfl⟩ := List.mem_map.mp mem
  cases p with
  | ground =>
    change evaluate cellHead (0 ::ᵥ nil) ∈ finiteCodes P
    have nilHead : evaluate cellHead (0 ::ᵥ nil) = 0 := rfl
    rw [nilHead]
    exact List.mem_map.mpr ⟨.ground, inP, rfl⟩
  | arrow d c =>
    have equation : run cellHead (code (.arrow d c)) = code d :=
      (headTailOfCell (cellAt (code d) (code c))).1
    change run cellHead (code (.arrow d c)) ∈ finiteCodes P
    rw [equation]
    exact List.mem_map.mpr ⟨d, closed d c inP, rfl⟩

theorem exact_OpenLiteralFiniteDomain : OpenLiteralFiniteDomain := by
  intro P closed B α Γ dom cod arrowIn
  obtain ⟨row⟩ := canonicalCell (body := B) (Γ := Γ) dom cod
  exact exact_FiniteProgramImageTransfer cellHead (finiteCodes P) (finiteCodes P)
    (headOfCodes P closed) B α Γ (rawCons dom cod) dom arrowIn
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight row)⟩

#print axioms exact_OriginalWindowDomain
#print axioms exact_OpenLiteralFiniteDomain

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureProofV2
