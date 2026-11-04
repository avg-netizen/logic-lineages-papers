module
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteTargets
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open ParametricSourceSuccessor

theorem finiteDenotation : Targets.FiniteDenotation := by
  intro ι G ν t hν ht
  induction t with
  | var i => exact hν i
  | zero => exact ⟨0,rfl⟩
  | one => exact ⟨1,by simp [denoteWith]⟩
  | omega => exact False.elim ht
  | add a b iha ihb =>
    obtain ⟨m,hm⟩ := iha ht.1
    obtain ⟨n,hn⟩ := ihb ht.2
    refine ⟨m+n,?_⟩
    change ordinalNaturalSum (denoteWith G ν a) (denoteWith G ν b)=_
    rw [hm,hn]
    exact naturalSum_finite m n
  | emul a b iha ihb =>
    obtain ⟨m,hm⟩ := iha ht.1
    obtain ⟨n,hn⟩ := ihb ht.2
    refine ⟨2^m*n,?_⟩
    change ordinalNaturalProduct ((2 : Ordinal)^denoteWith G ν a) (denoteWith G ν b)=_
    rw [hm,hn]
    have hp : (2 : Ordinal)^(m : Ordinal)=((2^m : Nat) : Ordinal) := by
      simpa only [Ordinal.opow_natCast,Nat.cast_ofNat] using (Ordinal.natCast_pow 2 m).symm
    rw [hp]
    exact naturalProduct_finite (2^m) n
  | collapse a b _ _ =>
    exact ⟨_,rfl⟩
end LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Proof
