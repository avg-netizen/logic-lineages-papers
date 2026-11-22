module
public import LogicLineages.PermittedControl.AffineCollapseTopologicalLowTargets
import LogicLineages.PermittedControl.AffineCollapseTopologicalLowProjectionProof
import LogicLineages.PermittedControl.AffineCollapseTopologicalExtensionLocalityProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseTopologicalLow
open AffineCollapseTopologicalExtension (Valuation AgreesOutside knownNotBorn)

theorem exactTopologicalExternalLow : ExactTopologicalExternalLow := by
  intro f B sel known pairs top limit base rank bound outside prior testRows test positive
  let projected : Valuation → Prop :=
    fun final => AgreesOutside pairs (Function.update base rank (final rank)) final ∧
      prior (Function.update base rank (final rank)) final
  have projectedAt (shared : Valuation) (a : Nat) :
      projected (Function.update shared rank a) ↔
        AgreesOutside pairs (Function.update base rank a) (Function.update shared rank a) ∧
          prior (Function.update base rank a) (Function.update shared rank a) := by
    change (AgreesOutside pairs (Function.update base rank ((Function.update shared rank a) rank))
        (Function.update shared rank a) ∧
      prior (Function.update base rank ((Function.update shared rank a) rank))
        (Function.update shared rank a)) ↔ _
    rw [Function.update_self]
  have checked (a : Nat) :=
    exactTestedExternalExtension f B sel known pairs top (Function.update base rank a)
      prior testRows test positive
  have exterior := knownNotBorn known pairs top rank outside
  have sliced (shared : Valuation) :=
    AffineCollapsePairListLow.exactFiniteListLow f shared projected pairs limit
      rank bound testRows test positive
  constructor
  · rintro ⟨a,within,final,ran,pr,values,actual,holds⟩
    obtain ⟨final',graphs,agree,priorAt,values',actual',holds'⟩ :=
      (checked a).mp ⟨final,ran,pr,values,actual,holds⟩
    obtain ⟨shared,hShared,hFactor⟩ := factorExternalUpdate pairs base final' rank a exterior agree
    rw [← hFactor] at graphs agree priorAt actual' holds'
    have hProj := (projectedAt shared a).mpr ⟨agree,priorAt⟩
    obtain ⟨branch,residual,member,hit,hPr,vals,snap,testOK⟩ :=
      (sliced shared).mp ⟨a,within,hProj,graphs,values',actual',holds'⟩
    have hPrior := ((projectedAt shared branch.1).mp hPr).2
    exact ⟨branch,residual,member,hit,shared,hShared,hPrior,vals,snap,testOK⟩
  · rintro ⟨branch,residual,member,hit,shared,sharedAgree,pr,values,snap,holds⟩
    have hProj := (projectedAt shared branch.1).mpr
      ⟨sameExternalUpdate pairs base shared rank branch.1 sharedAgree,pr⟩
    obtain ⟨a,within,hPr,graphs,vals,actual,testOK⟩ :=
      (sliced shared).mpr ⟨branch,residual,member,hit,hProj,values,snap,holds⟩
    have hJoint := (projectedAt shared a).mp hPr
    refine ⟨a,within,(checked a).mpr ?_⟩
    exact ⟨Function.update shared rank a,graphs,hJoint.1,hJoint.2,vals,actual,testOK⟩

end LogicLineages.PermittedControl.AffineCollapseTopologicalLow
