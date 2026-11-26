import LogicLineages.PersistentMarking.MarkedFamilyParameters
namespace LogicLineages.PersistentMarking.MarkedFamilyParameterTargets
open Spine NameBridge DecisionPorts DecisionInventory DecisionSourceUniverse FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedFamilyParameters

def Enumeration : Prop := ∀ E heads p, p ∈ parameters E heads ↔ Valid E heads p

def Distinct : Prop := ∀ E heads, (parameters E heads).Pairwise (· ≠ ·)

def SchemaExact : Prop := ∀ E heads p n,
  (p,n) ∈ MarkedFamilyParameters.schema E heads ↔ Valid E heads p ∧ n = ((descriptor E p.2.1).carriers p.2.2.1).length

def SchemaDistinct : Prop := ∀ E heads, ((MarkedFamilyParameters.schema E heads).map Prod.fst).Pairwise (· ≠ ·)

/- No caller-provided declaration coverage: derive K coverage from actual inputs. -/
def SourceCoverage : Prop := ∀ s t σ τ,
  Typed EmptyContext s σ → Typed EmptyContext t τ → Ordinary s → Ordinary t →
  ∀ f, f ∈ (inventory s t).sourceHeads →
    f.result ∈ (inventory s t).types ∧ (∀ ρ, ρ ∈ f.arguments → ρ ∈ (inventory s t).types)
end LogicLineages.PersistentMarking.MarkedFamilyParameterTargets
