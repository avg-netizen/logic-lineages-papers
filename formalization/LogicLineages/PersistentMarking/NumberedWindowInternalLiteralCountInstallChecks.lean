module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallSelectedProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountInstallChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedListInstallSelectedProof (exact_SelectedReinstallTypedList)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)

/-- The selected evaluator, original interpretation and original rules
are rebuilt on this new literal jRaw/dCore tuple, without a CountFit premise.
This is not an open membership- or occurrence-transport assertion. -/
theorem exact_SelectedLiteralCountTypedListInstall (xs : Entries) (s : Settings) :
    ∃ (i : Program 1) (r : Program 3), Reinstalled xs s i (jRaw i) r permutation :=
  exact_SelectedReinstallTypedList xs s permutation exact_OriginalLiteralCountFit

#print axioms exact_SelectedLiteralCountTypedListInstall
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountInstallChecks
