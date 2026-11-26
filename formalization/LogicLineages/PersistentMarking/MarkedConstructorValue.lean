import LogicLineages.PersistentMarking.MarkedConstructorTests
namespace LogicLineages.PersistentMarking.MarkedConstructorValue
open Spine NameBridge DecisionPorts HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)

/-- New observation fields; all premises and tuple outputs read only previous M. -/
def build (S : Signature) (E : Environment) (heads : List Head) (M : FiniteDomainSchema.Code) (p : Parameter) : Value where
  available _ := true
  weak Δ t := MarkedConstructorTests.weakTest S E heads M (MarkedFamilyCoherence.weakenParameter E p Δ) t
  strict Δ t := MarkedConstructorTests.weakTest S E heads M (MarkedFamilyCoherence.weakenParameter E p Δ) t
  application Δ ds τ xs :=
    let w := MarkedFamilyCoherence.weakenParameter E p Δ
    ProtectedSpineEnvironment.originalHeadCall E heads M Δ p.1 p.2.1 w.2.2.2.1 w.2.2.2.2 ds xs τ
end LogicLineages.PersistentMarking.MarkedConstructorValue
