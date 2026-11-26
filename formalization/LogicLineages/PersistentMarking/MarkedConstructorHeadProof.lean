import LogicLineages.PersistentMarking.MarkedConstructorOccurrenceProof
namespace LogicLineages.PersistentMarking.MarkedConstructorHeadProof
open Spine NameBridge DecisionPorts HereditaryDomainCode MarkedConstructorTargets

theorem precedes (S : Signature) (f g : Head) :
    MarkedConstructorTests.precedes S f g = true ↔ Precedes S f g := by
  cases hf : classRank S f <;> cases hg : classRank S g <;>
    simp [MarkedConstructorTests.precedes,Precedes,hf,hg]

theorem equivalent (S : Signature) (f g : Head) :
    MarkedConstructorTests.equivalent S f g = true ↔ Equivalent S f g := by
  cases hf : classRank S f <;> cases hg : classRank S g <;>
    simp [MarkedConstructorTests.equivalent,Equivalent,hf,hg]

theorem whole (E : Environment) (heads : List Head) (M : FiniteDomainSchema.Code)
    (p : MarkedFamilyParameters.Parameter) (ts : List Expr) :
    MarkedConstructorTests.whole E heads M p ts = true ↔ WholeWitness E heads M p ts := by
  simp only [MarkedConstructorTests.whole,List.all_eq_true,WholeWitness]
  apply forall_congr'; intro t
  apply forall_congr'; intro _
  cases h : MarkedConstructorTests.owner E heads M p t.type <;> simp [h]

theorem copy : MarkedConstructorTargets.CopyExact := by
  intro S E heads M p t
  cases t <;> simp [MarkedConstructorTests.copyTest,precedes,whole]

theorem stat : MarkedConstructorTargets.StatExact := by
  intro S E heads M p t
  cases t <;> simp [MarkedConstructorTests.statTest,equivalent,whole,
    MarkedConstructorOccurrenceProof.multiset, and_assoc]
end LogicLineages.PersistentMarking.MarkedConstructorHeadProof
