module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorOccurrenceProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorHeadExactProof
open Spine NameBridge DecisionPorts HereditaryDomainCode MarkedConstructorTargets

theorem precedes (S : Signature) (f g : Head) :
    MarkedConstructorTests.precedes S f g = true ↔ Precedes S f g := by
  cases hf : classRank S f <;> cases hg : classRank S g <;>
    simp [MarkedConstructorTests.precedes,Precedes,hf,hg]

theorem equivalent (S : Signature) (f g : Head) :
    MarkedConstructorTests.equivalent S f g = true ↔ Equivalent S f g := by
  cases hf : classRank S f <;> cases hg : classRank S g <;>
    simp [MarkedConstructorTests.equivalent,Equivalent,hf,hg,eq_comm]

theorem whole (E : Environment) (heads : List Head) (M : FiniteDomainSchema.Code)
    (p : MarkedFamilyParameters.Parameter) (ts : List Expr) :
    MarkedConstructorTests.whole E heads M p ts = true ↔ WholeWitness E heads M p ts := by
  simp only [MarkedConstructorTests.whole,List.all_eq_true,WholeWitness]
  apply forall_congr'; intro t
  apply forall_congr'; intro _
  cases MarkedConstructorTests.owner E heads M p t.type <;> simp

theorem copy : CopyExact := by
  intro S E heads M p t
  cases t <;> simp [MarkedConstructorTests.copyTest]
  rename_i f args
  simp only [precedes, whole]
  constructor
  · rintro ⟨⟨ht, hr⟩, hw⟩
    exact ⟨f, args, ⟨rfl, rfl⟩, ht, hr, hw⟩
  · rintro ⟨g, ts, ⟨rfl, rfl⟩, ht, hr, hw⟩
    exact ⟨⟨ht, hr⟩, hw⟩

theorem stat : StatExact := by
  intro S E heads M p t
  cases t <;> simp [MarkedConstructorTests.statTest]
  rename_i f args
  have hMultiset := MarkedConstructorOccurrenceProof.multiset E p.2.2.1
    (p.1.arguments.zip p.2.2.2.1) (MarkedConstructorTests.terms args)
  simp only [equivalent, whole, hMultiset]
  constructor
  · rintro ⟨⟨⟨ht, hr⟩, hm⟩, hw⟩
    exact ⟨f, args, ⟨rfl, rfl⟩, ht, hr, hm, hw⟩
  · rintro ⟨g, ts, ⟨rfl, rfl⟩, ht, hr, hm, hw⟩
    exact ⟨⟨⟨ht, hr⟩, hm⟩, hw⟩

theorem exact_CopyExact : CopyExact := copy
theorem exact_StatExact : StatExact := stat
#print axioms exact_CopyExact
#print axioms exact_StatExact
end LogicLineages.PersistentMarking.MarkedConstructorHeadExactProof
