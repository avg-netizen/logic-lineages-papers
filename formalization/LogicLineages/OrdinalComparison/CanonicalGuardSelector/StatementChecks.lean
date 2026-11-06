module
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.BridgeProof
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector.StatementChecks

theorem fixed_canonicalCalibration : Targets.CanonicalCalibration := Proof.canonicalCalibration
theorem fixed_viewSyntax : Targets.ViewSyntax := Proof.viewSyntax
theorem fixed_viewCorrect : Targets.ViewCorrect := Proof.viewCorrect
theorem fixed_viewTailCorrect : Targets.ViewTailCorrect := Proof.viewTailCorrect
theorem fixed_viewMeasure : Targets.ViewMeasure := Proof.viewMeasure
theorem fixed_caseSound : Targets.CaseSound := Proof.caseSound
theorem fixed_localSelectionCorrect : Targets.LocalSelectionCorrect := Proof.localSelectionCorrect
theorem fixed_selectionCoverage : Targets.SelectionCoverage := Proof.selectionCoverage
theorem fixed_selectedChildCorrect : Targets.SelectedChildCorrect := Proof.selectedChildCorrect
theorem fixed_selectorPrograms : Targets.SelectorPrograms := Proof.selectorPrograms

#print axioms fixed_canonicalCalibration
#print axioms fixed_viewSyntax
#print axioms fixed_viewCorrect
#print axioms fixed_viewTailCorrect
#print axioms fixed_viewMeasure
#print axioms fixed_caseSound
#print axioms fixed_localSelectionCorrect
#print axioms fixed_selectionCoverage
#print axioms fixed_selectedChildCorrect
#print axioms fixed_selectorPrograms

end LogicLineages.OrdinalComparison.CanonicalGuardSelector.StatementChecks
