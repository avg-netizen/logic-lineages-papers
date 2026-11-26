module
public import LogicLineages.PermittedControl.StandardFunctionalHardnessTargets
public import LogicLineages.PermittedControl.StandardFiniteQueryProof
public import LogicLineages.PermittedControl.StandardSingleQueryProof
public import LogicLineages.PermittedControl.SelectedDecisionPullbackProof
public import LogicLineages.PermittedControl.SelectedFunctionalHardnessProof
public import LogicLineages.PermittedControl.PolynomialUndecidabilitySupplierProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalHardness.Proof
open OrdinalComparison Source Source.AdmissibleSum
open Source.FunctionalHardnessCompletion

/-- Both decision pullbacks quantify an arbitrary control and carry no
selected-control hypothesis; every reduction used here is the Phi reduction. -/
theorem standardFunctionalHardness : StandardFunctionalHardness.StandardFunctionalHardness := by
  intro policy
  obtain ⟨hfs,hfw⟩ := StandardFiniteQuery.Proof.bothReductions policy
  obtain ⟨hss,hsw⟩ := StandardSingleQuery.Proof.bothReductions policy
  have hu := PolynomialUndecidabilitySupplier.Proof.polynomialUndecidabilitySupplier.2
  exact ⟨hfs,hfw,
    fun hd => hu (SelectedDecisionPullback.Proof.finiteQueryPullback Phi policy true hfs hd),
    fun hd => hu (SelectedDecisionPullback.Proof.finiteQueryPullback Phi policy false hfw hd),
    hss,hsw,
    fun hd => hu (SelectedFunctionalHardness.Proof.singleQueryPullback Phi policy true hss hd),
    fun hd => hu (SelectedFunctionalHardness.Proof.singleQueryPullback Phi policy false hsw hd)⟩
end LogicLineages.PermittedControl.StandardFunctionalHardness.Proof
