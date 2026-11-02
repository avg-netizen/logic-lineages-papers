module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess LambdaObservationMatching LiteralWorldTransport

def ConsPortTransport : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (σ : Ty) (i : Fin (budget I))
    (hQ : (i,σ)::P.val ∈ worldList I) (τ : Ty) (v : Variable (portTypes P.val++I.context) τ),
    LiteralVariableValue.extendVariables I.context ((i,σ)::P.val) P.val (fun p hp => List.mem_cons_of_mem _ hp) v=v.there

def OpeningIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (σ υ : Ty) (i : Fin (budget I)) (h : MarkedFAbsTest.Opening I P σ υ i),
    @Eq (Environment I (σ::(portTypes P.val++I.context)) ⟨(i,σ)::P.val,h.2.1⟩)
      (openingEnvironment (identity I P) σ υ i h) (identity I ⟨(i,σ)::P.val,h.2.1⟩)

def SourceIdentityWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (P Q : World I) (h : Extends P Q)
    (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) τ),
    interpret (weakenSource h q) M Q (identity I Q)=RecursiveNaturalDomains.weaken h (interpret q M P (identity I P))

def SourceReadTransport : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (P Q : World I) (h : Extends P Q)
    (τ : Ty) (q : ConfinedTerm I (portTypes P.val++I.context) τ) (strict : Bool)
    (o : Observation Symbol arity I.context (budget I)),(∀ p ∈ Q.val,p ∈ o.ports) →
    readBit strict (interpret (weakenSource h q) M Q (identity I Q)) o=readBit strict (interpret q M P (identity I P)) o

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportTargets
