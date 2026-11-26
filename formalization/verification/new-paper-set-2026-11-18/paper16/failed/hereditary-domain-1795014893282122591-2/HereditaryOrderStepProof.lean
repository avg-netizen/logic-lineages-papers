import LogicLineages.PersistentMarking.HereditaryCodeOrderProof
import LogicLineages.PersistentMarking.HereditaryEncodingCongruenceProof
import LogicLineages.PersistentMarking.HereditarySemanticOrderProof
import LogicLineages.PersistentMarking.HereditaryDecodedValidityProof
namespace LogicLineages.PersistentMarking.HereditaryOrderStepProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryOrderTargets

theorem step : OrderStep := by
  intro E σ lower Γ hw
  have laws := HereditarySemanticOrderProof.laws E σ Γ hw lower
  constructor
  · intro a ha
    exact (HereditaryCodeOrderProof.exactOrder E σ Γ a a hw ha ha).mpr
      (laws.1 _ (HereditaryDecodedValidityProof.valid E σ Γ a hw ha))
  constructor
  · intro a b c ha hb hc hab hbc
    exact (HereditaryCodeOrderProof.exactOrder E σ Γ a c hw ha hc).mpr
      (laws.2.1 _ _ _ (HereditaryDecodedValidityProof.valid E σ Γ a hw ha)
        (HereditaryDecodedValidityProof.valid E σ Γ b hw hb)
        (HereditaryDecodedValidityProof.valid E σ Γ c hw hc)
        ((HereditaryCodeOrderProof.exactOrder E σ Γ a b hw ha hb).mp hab)
        ((HereditaryCodeOrderProof.exactOrder E σ Γ b c hw hb hc).mp hbc))
  · intro a b ha hb hab hba
    apply HereditaryEncodingCongruenceProof.injective E σ Γ a b ha hb
    exact laws.2.2 _ _ (HereditaryDecodedValidityProof.valid E σ Γ a hw ha)
      (HereditaryDecodedValidityProof.valid E σ Γ b hw hb)
      ((HereditaryCodeOrderProof.exactOrder E σ Γ a b hw ha hb).mp hab)
      ((HereditaryCodeOrderProof.exactOrder E σ Γ b a hw hb ha).mp hba)

end LogicLineages.PersistentMarking.HereditaryOrderStepProof
