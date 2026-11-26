module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilitySuccessorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityCoreProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication InternalAccessibilityRules
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionClosureLogicProof (closedApply)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalVariableObject OriginalVariableComputability UniformCertificateCompletion

/-- Apply genuine original neutral expansion to the internally proved
computable successors. Scalar I alone is never substituted for arrow C. -/
theorem variableComputable (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) :
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    let src := GlobalSourcePackage.source p
    let comp := GlobalSourcePackage.computability p
    VariableCertificateBottom src comp context →
    OriginalNeutralExpansion.NeutralComputabilityExpansion src comp context →
    VariableComputable src comp context := by
  dsimp only
  intro hbottom hneutral tau alpha Gamma object
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := GlobalSourcePackage.source p
  let comp := GlobalSourcePackage.computability p
  let H := typed comp tau (numeral context) object ⊓ variableObject object
  have hh : Nonempty (Derivation (SourcePresentation.sourceBody src context) (H :: Gamma) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hn := OriginalVariableComputabilityShapeProof.nonLambda object (andRight hh)
  have hs := OriginalVariableComputabilitySuccessorsProof.successorsFromCertificates src comp context tau
    (OriginalVariableComputabilitySuccessorsProof.certificateComputable n arity p hp
      symbols S table hS hbottom tau) alpha (H :: Gamma) object (andLeft hh) (andRight hh)
  obtain ⟨hc⟩ := closedApply (hneutral tau alpha [] object)
    (andIntro (andLeft hh) (andIntro hn hs))
  exact ⟨Derivation.implicationIntroduction hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityCoreProof
