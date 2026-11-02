module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom

def Enumerated : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I), bottomValue I τ P ∈ enumerateValues I τ P

def Least : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P), bottomValue I τ P ≤ a

def UniqueLeast : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P), (∀ b,a ≤ b) ↔ a=bottomValue I τ P

def WeakeningBottom : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q), RecursiveNaturalDomains.weaken h (bottomValue I τ P)=bottomValue I τ Q

def AllBitsFalse : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I), (layerView I τ P (bottomValue I τ P)).val.1=(fun _ => (false,(fun _ => false),(fun _ => false)))

def AllTablesBottom : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (Q : Future P) (s : Suffix τ) (v : FullTuple I τ s Q.val), (layerView I τ P (bottomValue I τ P)).val.2 Q s v=bottomValue I s.val.2 Q.val

end LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottomTargets
