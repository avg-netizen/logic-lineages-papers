import LogicLineages.PersistentMarking.MarkedConstructorOperatorTargets

namespace LogicLineages.PersistentMarking.MarkedConstructorSourceLookupTargets
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations FiniteDomainFoundation
open HereditaryDomainCode HereditaryDomainSemantics MarkedConstructorOperator
open MarkedFamilyParameters (Parameter)

def SourceLookup (S : Signature) (s t : Expr) (σ τ : Ty) : Prop :=
  PaperTerm S s σ → PaperTerm S t τ → Ordinary s → Ordinary t →
  let E := environment s t
  let heads := (inventory s t).sourceHeads
  ∀ M p, M ∈ MarkedFamilyCoherence.retained E heads → MarkedFamilyParameters.Valid E heads p →
    (∀ a, a ∈ p.1.arguments.zip p.2.2.2.1 ++ p.2.2.2.2 →
      ∀ ds υ, (ds,υ) ∈ fullPrefixes a.1 →
        ∃ xs, MarkedConstructorTests.ownerTuple E heads M p ds = some xs ∧
          TupleValues E p.2.2.1 ds xs ∧
          StructuralActions.fullAction E a.1 p.2.2.1 a.2 ds υ xs ∈ (descriptor E υ).carriers p.2.2.1) ∧
    (∀ g ts, Expr.head g ts ∈ observations E.names E.ports p.2.2.1 E.target p.2.1 →
      ∀ u, u ∈ MarkedConstructorTests.terms ts →
        ∃ c, MarkedConstructorTests.owner E heads M p u.type = some c ∧
          c ∈ (descriptor E u.type).carriers p.2.2.1) ∧
    (∀ α β body, p.2.1 = .arrow α β →
      Expr.lam α body ∈ observations E.names E.ports p.2.2.1 E.target p.2.1 →
      ∃ i c, ProtectedSpineEnvironment.openingSlot p.2.2.1 = some i ∧
        let Θ := ProtectedSpineEnvironment.openingContext p.2.2.1 α i
        WellFormed E.types E.ports Θ ∧ Extends p.2.2.1 Θ ∧ used Θ = used p.2.2.1 + 1 ∧
        openBody α (portName E.names i) body ∈ observations E.names E.ports Θ E.target β ∧
        StructuralActions.markedAction E heads M (MarkedConstructorTests.fabsParameter E p α β i) = some c ∧
        c ∈ (descriptor E β).carriers Θ)

def SourceLookupExact : Prop := ∀ S s t σ τ, SourceLookup S s t σ τ

end LogicLineages.PersistentMarking.MarkedConstructorSourceLookupTargets
