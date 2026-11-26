module
public import LogicLineages.PermittedControl.SelectedLevelTwoTargets
public import LogicLineages.PermittedControl.SelectedFiniteQueryProof
public import LogicLineages.PermittedControl.SelectedDecisionPullbackProof
public import LogicLineages.PermittedControl.PolynomialUndecidabilitySupplierProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedLevelTwo.Proof
 theorem selectedLevelTwo : SelectedLevelTwoTargets.SelectedLevelTwo := by
  intro ctrl K hc policy
  obtain ⟨hs,hw⟩ := SelectedFiniteQuery.Proof.bothReductions ctrl K hc policy
  have hu := PolynomialUndecidabilitySupplier.Proof.polynomialUndecidabilitySupplier.2
  exact ⟨hs,hw,
    fun hd => hu (SelectedDecisionPullback.Proof.finiteQueryPullback ctrl policy true hs hd),
    fun hd => hu (SelectedDecisionPullback.Proof.finiteQueryPullback ctrl policy false hw hd)⟩
end LogicLineages.PermittedControl.SelectedLevelTwo.Proof
