module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueTargets
open Source Source.SourceTypedPorts Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom LiteralVariableValue

def NameInjective : Prop := ∀ (B : Nat) (Γ : List Ty) (P : PortContext B), (P.map Prod.fst).Nodup → ∀ (τ : Ty) (v w : Variable (portTypes P ++ Γ) τ), variableName Γ P v=variableName Γ P w → v=w

def NameExtension : Prop := ∀ (B : Nat) (Γ : List Ty) (P Q : PortContext B) (h : ∀ p ∈ P,p ∈ Q) (τ : Ty) (v : Variable (portTypes P ++ Γ) τ), variableName Γ Q (extendVariables Γ Q P h v)=variableName Γ P v

def LiteralWeakBits : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (v : Variable (portTypes P.val ++ I.context) τ) (Q : Future P) (o : ObservationAt I τ Q.val), ((variableRaw v).1 Q).2.1 o=true ↔ observationName o.val=some (variableName I.context P.val v)

def AvailabilityAndStrict : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (v : Variable (portTypes P.val ++ I.context) τ) (Q : Future P), ((variableRaw v).1 Q).1=true ∧ ∀ o,((variableRaw v).1 Q).2.2 o=false

def UndefinedTables : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (v : Variable (portTypes P.val ++ I.context) τ) (Q : Future P) (s : Suffix τ) (a : FullTuple I τ s Q.val), (variableRaw v).2 Q s a=bottomValue I s.val.2 Q.val

def NaturalVariable : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (v : Variable (portTypes P.val ++ I.context) τ), NaturalTupleLayer.Good (variableRaw v)

def VariableWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (v : Variable (portTypes P.val ++ I.context) τ), rawWeaken h (variableRaw v)=variableRaw (extendVariables I.context Q.val P.val h v)

def ActualValue : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (v : Variable (portTypes P.val ++ I.context) τ), ∃ a : Value I τ P,(layerView I τ P a).val=variableRaw v

def LiteralVariableEquality : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (v : Variable (portTypes P.val ++ I.context) τ) (Q : Future P) (o : ObservationAt I τ Q.val), ((variableRaw v).1 Q).2.1 o=true ↔ o.val=⟨Q.val.val,τ,.var (extendVariables I.context Q.val.val P.val Q.property v)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueTargets
