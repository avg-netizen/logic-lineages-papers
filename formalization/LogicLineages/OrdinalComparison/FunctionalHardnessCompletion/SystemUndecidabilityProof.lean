module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemUndecidabilityH10Export
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemUndecidabilityRootExport
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.Proof

private theorem computablePredPreimage {p : Nat → Prop} (hp : ComputablePred p)
    (f : Nat → Nat) (hf : Computable f) : ComputablePred (fun x => p (f x)) := by
  obtain ⟨dp,hp⟩ := hp
  exact ⟨fun x => dp (f x),hp.comp hf⟩

/-- Transfer from the proved integer-polynomial/Nat-root problem along the
proved total map. These are distinct languages linked by a genuine reduction. -/
theorem polynomialSystemUndecidable : UndecidabilityTargets.PolynomialSystemUndecidable := by
  intro h
  apply RootExport.undecidable
  obtain ⟨reduce,hcomp,hcorrect⟩ := H10Export.bridge
  exact (computablePredPreimage h reduce hcomp).of_eq (fun e => (hcorrect e).symm)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.Proof
