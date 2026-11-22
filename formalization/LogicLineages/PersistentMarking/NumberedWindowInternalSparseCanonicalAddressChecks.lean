module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (reportsCases)
open NumberedWindowInternalSparseCanonicalCoordinatesChecks (exact_CanonicalPositive)
open NumberedWindowInternalSparseCanonicalAddressTargets

theorem exact_AddressScalarCalibration : ExactAddressScalarCalibration :=
  NumberedWindowInternalSparseCanonicalAddressNumericProof.calibration

theorem exact_ReportedAddressScalar : ExactReportedAddressScalar :=
  NumberedWindowInternalSparseCanonicalAddressFieldsProof.reported

theorem exact_PositiveAddressCarriers : ExactPositiveAddressCarriers := by
  intro C s baseX baseW root other syntaxProg cv tv body α Γ a cert b W X least raw i
  let A := programGraph (addressPositive cv tv raw least) (suc z) ![a,cert,b]
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have actual := forward cv tv raw least a cert b ⟨h⟩
  have result : Nonempty (Derivation body Δ (unary i (suc z) a ⊓ unary i (suc z) b)) := by
    apply reportsCases cv tv raw least a cert b _ actual
    intro β j Θ ctx ty src dst _ facts
    simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel]
    obtain ⟨row⟩ := facts
    have rest := Derivation.conjunctionRight row
    have guards := Derivation.conjunctionRight rest
    obtain ⟨law⟩ := exact_CanonicalPositive C s baseX baseW root other syntaxProg body β Θ ctx ty src (cert.relabel j) dst
    have endpoints := Derivation.implicationElimination law (Derivation.conjunctionRight (Derivation.conjunctionRight guards))
    obtain ⟨left⟩ := exact_ReportedAddressScalar cv tv W least body β Θ (a.relabel j) ctx ty src
    obtain ⟨right⟩ := exact_ReportedAddressScalar cv tv W least body β Θ (b.relabel j) ctx ty dst
    have c := Derivation.conjunctionLeft guards
    have t := Derivation.conjunctionLeft (Derivation.conjunctionRight guards)
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (Derivation.conjunctionRight (Derivation.implicationElimination left
        (Derivation.conjunctionLeft row))) (Derivation.conjunctionIntroduction c
        (Derivation.conjunctionIntroduction t (Derivation.conjunctionLeft endpoints))))
      (Derivation.implicationElimination (Derivation.conjunctionRight (Derivation.implicationElimination right
        (Derivation.conjunctionLeft rest))) (Derivation.conjunctionIntroduction c
        (Derivation.conjunctionIntroduction t (Derivation.conjunctionRight endpoints))))⟩
  obtain ⟨d⟩ := result
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_AddressScalarCalibration
#print axioms exact_ReportedAddressScalar
#print axioms exact_PositiveAddressCarriers
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressChecks
