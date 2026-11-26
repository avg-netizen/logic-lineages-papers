module
public import LogicLineages.PermittedControl.SelectedFunctionalHardnessTargets
public import LogicLineages.PermittedControl.SelectedLevelTwoProof
public import LogicLineages.PermittedControl.SelectedSingleQueryProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalHardness.Proof
open OrdinalComparison Source Source.AdmissibleSum
open Source.FunctionalHardnessCompletion

 theorem singleQueryPullback (ctrl : Nat → Nat) (policy : Policy) (strict : Bool)
    (hr : SelectedSingleQuery.SingleQueryReduction ctrl policy strict)
    (hd : SelectedFiniteQuery.HasComparisonDecider ctrl policy 3 strict) :
    ComputablePred encodedPolynomialSolvable := by
  obtain ⟨reduce,hreduce,hsem⟩ := hr
  obtain ⟨answer,hanswer,hcorrect⟩ := hd
  have hbool : Computable (fun e => answer (reduce e)) := hanswer.comp hreduce
  have hmeaning : ∀ e, ¬encodedPolynomialSolvable e ↔ answer (reduce e)=true := by
    intro e
    obtain ⟨Γ,a,b,hcode,hΓ,ha,hb,he⟩ := hsem e
    rw [←hcode]
    exact he.trans (hcorrect Γ a b hΓ ha hb).symm
  have hcomplement : ComputablePred (fun e => ¬encodedPolynomialSolvable e) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨(fun e => answer (reduce e)),hbool,?_⟩
    exact funext (fun e => propext (hmeaning e))
  exact hcomplement.not.of_eq (fun e => by simp)

 theorem selectedFunctionalHardness : SelectedFunctionalHardnessTargets.SelectedFunctionalHardness := by
  intro ctrl K hc policy
  obtain ⟨hfs,hfw,hns,hnw⟩ := SelectedLevelTwo.Proof.selectedLevelTwo ctrl K hc policy
  obtain ⟨hss,hsw⟩ := SelectedSingleQuery.Proof.bothReductions ctrl K hc policy
  have hu := PolynomialUndecidabilitySupplier.Proof.polynomialUndecidabilitySupplier.2
  exact ⟨hfs,hfw,hns,hnw,hss,hsw,
    fun hd => hu (singleQueryPullback ctrl policy true hss hd),
    fun hd => hu (singleQueryPullback ctrl policy false hsw hd)⟩
end LogicLineages.PermittedControl.SelectedFunctionalHardness.Proof
