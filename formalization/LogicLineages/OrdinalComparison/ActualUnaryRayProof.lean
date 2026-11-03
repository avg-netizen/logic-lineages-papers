module
public import LogicLineages.OrdinalComparison.ActualUnaryRayTargets
public import LogicLineages.OrdinalComparison.ActualUnaryRayAssignmentProof
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
public import LogicLineages.OrdinalComparison.SourceUnitEliminationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualUnaryRay.Proof
open ForwardTranslation OriginalDomain

theorem genuineRayAndComputability : Targets.GenuineRayAndComputability := by
  intro a c
  have he (n : Nat) : rayValue a c n =
      actualCollapse (fixedHead a + ((c+1+n : Nat) : Ordinal)) := by
    have hn : actualOrdinalNorm (fixedHead a)+c+1+n-actualOrdinalNorm (fixedHead a) = c+1+n := by omega
    simp only [rayValue,totalNorm,actualHeadValue,actualHeadInitial,hn]
  refine ⟨?_,fun n => ⟨by unfold totalNorm; omega,he n⟩⟩
  exact ((scalarFixedShiftComputable a).comp
    (Primrec.nat_add.comp (Primrec.const (c+1)) Primrec.id).to_comp).of_eq (fun n => (he n).symm)

theorem actualRayObservation : Targets.ActualRayObservation := by
  intro Γ K
  obtain ⟨u,a,c,v,hconst,hv,hhead,hclosed,hray⟩ := actualSourceRay Γ K
  obtain ⟨q,hq,hground,heval⟩ := UnitElimination.Proof.fullSourceUnitElimination.2.2
    (.ground::Γ) .ground (source K)
  refine ⟨u,a,c,q,hconst,hq,hground,?_⟩
  intro ρ r
  rw [heval ρ r]
  constructor
  · rintro ⟨w,hw,hval⟩
    have hsame : w = v := Option.some.inj (hw.symm.trans hv)
    subst w
    have he := (hray ρ).symm.trans hval
    exact_mod_cast he.symm
  · intro he
    subst r
    exact ⟨v,hv,hray ρ⟩
end LogicLineages.OrdinalComparison.Source.ActualUnaryRay.Proof
