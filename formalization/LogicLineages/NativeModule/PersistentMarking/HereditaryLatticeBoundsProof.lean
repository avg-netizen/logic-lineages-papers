module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryLatticeClosureProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryAggregateOrderProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryValueEqualityProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryLatticeBoundsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets HereditaryLatticeClosureProof

theorem bounds (E : Environment) (σ : Ty) (lower : LowerLattice E σ) : JoinAt E σ ∧ MeetAt E σ := by
  constructor
  · intro Γ cs hw hc
    have hcl := closure E σ Γ false cs hw lower hc
    have ho := HereditaryAggregateOrderProof.order E σ Γ _ hw lower (inputsValid E σ Γ cs hw hc)
    refine ⟨hcl.1,?_,?_⟩
    · intro c hm
      apply (HereditaryCodeOrderProof.exactOrder E σ Γ c _ hw (hc c hm) hcl.1).mpr
      exact HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.refl E σ Γ _)
        (HereditaryValueEqualityProof.symm hcl.2) (ho.1 _ (List.mem_map.mpr ⟨c,hm,rfl⟩))
    · intro b hb hbound
      apply (HereditaryCodeOrderProof.exactOrder E σ Γ _ b hw hcl.1 hb).mpr
      apply HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.symm hcl.2)
        (HereditaryValueEqualityProof.refl E σ Γ _)
      apply ho.2.2.1 _ (HereditaryDecodedValidityProof.valid E σ Γ b hw hb)
      intro v hv; obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hv
      exact (HereditaryCodeOrderProof.exactOrder E σ Γ c b hw (hc c hm) hb).mp (hbound c hm)
  · intro Γ cs hw hc
    have hcl := closure E σ Γ true cs hw lower hc
    have ho := HereditaryAggregateOrderProof.order E σ Γ _ hw lower (inputsValid E σ Γ cs hw hc)
    refine ⟨hcl.1,?_,?_⟩
    · intro c hm
      apply (HereditaryCodeOrderProof.exactOrder E σ Γ _ c hw hcl.1 (hc c hm)).mpr
      exact HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.symm hcl.2)
        (HereditaryValueEqualityProof.refl E σ Γ _) (ho.2.1 _ (List.mem_map.mpr ⟨c,hm,rfl⟩))
    · intro b hb hbound
      apply (HereditaryCodeOrderProof.exactOrder E σ Γ b _ hw hb hcl.1).mpr
      apply HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.refl E σ Γ _)
        (HereditaryValueEqualityProof.symm hcl.2)
      apply ho.2.2.2 _ (HereditaryDecodedValidityProof.valid E σ Γ b hw hb)
      intro v hv; obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hv
      exact (HereditaryCodeOrderProof.exactOrder E σ Γ b c hw hb (hc c hm)).mp (hbound c hm)
end LogicLineages.PersistentMarking.HereditaryLatticeBoundsProof
