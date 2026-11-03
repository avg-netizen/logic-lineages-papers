module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerTargets
open Source Source.SourceArrowSuffixes Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer

def SuffixCalibration : Prop := ∀ (τ : Ty) (s : Suffix τ),
    s.val.1 ≠ [] ∧ arrows s.val.1 s.val.2=τ ∧ typeSize s.val.2 < typeSize τ ∧
    ∀ i : Fin s.val.1.length,typeSize (argumentType s i) < typeSize τ

def ExhaustiveEnumeration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P : World I) (a : Natural I τ D P),
    a ∈ enumerateNatural I τ D P

def WeakeningIdentity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P : World I) (a : Raw I τ D P),rawWeaken (fun _ hp => hp) a=a

def WeakeningComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P Q R : World I)
    (h : Extends P Q) (k : Extends Q R) (a : Raw I τ D P),
    rawWeaken k (rawWeaken h a)=rawWeaken (fun p hp => k p (h p hp)) a

def NaturalPreservation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P Q : World I)
    (h : Extends P Q) (a : Raw I τ D P),Good a → Good (rawWeaken h a)

def WeakeningMonotone : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (D : Lower I τ) (P Q : World I)
    (h : Extends P Q) (a b : Raw I τ D P),a ≤ b → rawWeaken h a ≤ rawWeaken h b

end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerTargets
