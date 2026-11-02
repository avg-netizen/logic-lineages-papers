module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets

def PackedOrder : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I),
    (∀ a : Packed I P,PackedLE a a) ∧
    (∀ a b c : Packed I P,PackedLE a b → PackedLE b c → PackedLE a c) ∧
    (∀ a b : Packed I P,PackedLE a b → PackedLE b a → a=b)

def FiberRepresentation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I),
    (∀ E : Extras I P,PackedDownClosed (contains E)) ∧
    ∀ S : Set (Packed I P),PackedDownClosed S → ∃! E : Extras I P,∀ a,contains E a ↔ a ∈ S

def ExhaustiveEnumeration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E : Extras I P),E ∈ enumerateExtras I P

def DownwardImage : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (E : Finset (Value I τ P)),DownClosed (imageFiber h E)

def ImageIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P : World I) (E : Down I τ P),imageFiber (fun _ hp => hp) E.val=E.val

def ImageComposition : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q R : World I) (h : Extends P Q) (k : Extends Q R) (E : Finset (Value I τ P)),
    imageFiber k (imageFiber h E)=imageFiber (fun p hp => k p (h p hp)) E

def ImageMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (τ : Ty) (P Q : World I) (h : Extends P Q) (E F : Finset (Value I τ P)),
    E ⊆ F → imageFiber h E ⊆ imageFiber h F

def PackedImageCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P Q : World I) (h : Extends P Q) (E : Extras I P) (b : Packed I Q),
    b.2 ∈ imageFiber h (E b.1).val ↔ ∃ a : Packed I P,contains E a ∧ PackedLE b (packedWeaken h a)

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsetsTargets
