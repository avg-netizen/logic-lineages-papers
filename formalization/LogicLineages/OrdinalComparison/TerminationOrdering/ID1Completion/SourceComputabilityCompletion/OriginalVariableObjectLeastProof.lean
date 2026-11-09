module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalAccessibilityRulesProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalVariableObject
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual scalar I introduction for the original Object. Every original
certificate successor has already been proved a typed same-Gamma bottom;
both its least membership and the original source carrier are derived. -/
theorem least (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (base : Data) (oldStep : Program 4) (window : Program 1) (oldVertex oldResult : Program 5)
    (context : Nat) (hw : evaluate window (List.Vector.ofFn ![context]) = 1) :
    let src := OuterSelection.source oldSrc oldComp base oldStep window
    let comp := OuterSelection.computability oldComp base window oldVertex oldResult
    VariableCertificateBottom src comp context → VariableLeast src comp context := by
  dsimp only
  intro hbottom tau α Delta object
  let selected := OuterSelection.data base window
  let src := OuterSelection.source oldSrc oldComp base oldStep window
  let comp := OuterSelection.computability oldComp base window oldVertex oldResult
  let H := typed comp tau (numeral context) object ⊓ variableObject object
  have hh : Nonempty (Derivation (SourcePresentation.sourceBody src context) (H :: Delta) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hcarrier := OuterCarrierProof.typedCarrier oldSrc oldComp selected oldStep
    BottomRepresentative.bottomTest BottomSpineMeasure.measure window oldVertex oldResult
    context hw tau object (andLeft hh)
  have hsuccessors := OriginalVariableObjectLeastSupportProof.successorsFromCertificates src comp
    context tau
    (OriginalVariableObjectLeastSupportProof.certificateLeast oldSrc oldComp base oldStep
      window oldVertex oldResult context hw hbottom tau)
    α (H :: Delta) object (andLeft hh) (andRight hh)
  obtain ⟨h⟩ := actualOriginalAccessibilityIntroduction src false context α (H :: Delta) object
    hcarrier hsuccessors
  exact ⟨Derivation.implicationIntroduction h⟩

/-- The SAME once-refined global tuple is used at every finite window.
The externally calibrated window supplies its closed numeral equation;
all Object coordinates, certificates and successor membership stay internal. -/
theorem actualOriginalVariableObjectLeast :
    OriginalVariableObjectTargets.ActualOriginalVariableObjectLeast := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS
  let r := OriginalVariableRepresentative.refineInputs p
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hw : evaluate r.window (List.Vector.ofFn ![context]) = 1 :=
    GlobalSourceSpineLeastProof.windowEvaluation n p.window hp.2.1 symbols S table hS
  have hbottom : VariableCertificateBottom (GlobalSourcePackage.source r)
      (GlobalSourcePackage.computability r) context :=
    OriginalVariableObjectCertificateProof.actualOriginalVariableObjectCertificateBottom
      n arity p hp symbols S table hS
  exact least r.oldSrc r.oldComp r.base r.oldStep r.window r.oldVertex r.oldResult
    context hw hbottom

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastProof
