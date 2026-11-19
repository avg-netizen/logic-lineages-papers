import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessChecks

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassEdge
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowSimulationData NumberedWindowRawWitnessBits
open NumberedWindowArithmeticLeastClass NumberedWindowClassPathWitnessBits
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode

theorem sound {S K Γ τ src dst e} (he : classEdgeBit S K Γ τ src dst e = true) :
    ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧ ClassEdge x y := by
  simp only [classEdgeBit,Bool.and_eq_true,decide_eq_true_eq] at he
  obtain ⟨⟨hw,hSrc⟩,hDst⟩ := he
  have hStep : WindowStep S K (finiteC Γ) τ e.source e.target :=
    (NumberedWindowRawWitnessChecks.exact_CertifiedFiniteWindowStep
      S K Γ τ e.source e.target).mp ⟨e.witness,hw⟩
  let Q : WindowCarrier S K (finiteC Γ) τ := ⟨e.source,hStep.2.1⟩
  let R : WindowCarrier S K (finiteC Γ) τ := ⟨e.target,hStep.2.2⟩
  exact ⟨classOf Q,classOf R,⟨Q,rfl,hSrc⟩,⟨R,rfl,hDst⟩,⟨Q,R,rfl,rfl,hStep.1⟩⟩

theorem complete {S K Γ τ src dst} {x y : Class S K (finiteC Γ) τ}
    (hk : DecisionSourceUniverse.Closed K)
    (hSrc : ActualCodeAt S K Γ τ src x) (hDst : ActualCodeAt S K Γ τ dst y)
    (he : ClassEdge x y) : ∃ e, classEdgeBit S K Γ τ src dst e = true := by
  obtain ⟨Q,R,hQ,hR,hr⟩ := he
  have hStep : WindowStep S K (finiteC Γ) τ Q.val R.val := ⟨hr,Q.property,R.property⟩
  obtain ⟨w,hw⟩ := (NumberedWindowRawWitnessChecks.exact_CertifiedFiniteWindowStep
      S K Γ τ Q.val R.val).mpr hStep
  refine ⟨⟨Q.val,R.val,w⟩,?_⟩
  simp only [classEdgeBit,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨hw,atRep hk Q hQ hSrc⟩,atRep hk R hR hDst⟩

theorem exactEdge : ExactCertifiedNumericClassEdge := by
  intro S K Γ τ src dst hk
  exact ⟨fun ⟨e,h⟩ => sound h,fun ⟨_,_,hSrc,hDst,h⟩ => complete hk hSrc hDst h⟩

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassEdge
