module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsTargets
open Source FiniteObservationBits NaturalTupleLayer NaturalLayerBounds

def SupNatural : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (D : Lower I τ) (L : LowerBounds D) (P : World I) (S : Set (Natural I τ D P)),Good (supRaw L P S)

def InfNatural : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (D : Lower I τ) (L : LowerBounds D) (P : World I) (S : Set (Natural I τ D P)),Good (infRaw L P S)

def SupUniversal : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (D : Lower I τ) (L : LowerBounds D) (P : World I) (S : Set (Natural I τ D P)),
    IsLUB (Subtype.val '' S) (supRaw L P S)

def InfUniversal : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (D : Lower I τ) (L : LowerBounds D) (P : World I) (S : Set (Natural I τ D P)),
    IsGLB (Subtype.val '' S) (infRaw L P S)

def SupRestriction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (D : Lower I τ) (L : LowerBounds D) (P Q : World I) (h : Extends P Q) (S : Set (Natural I τ D P)),
    rawWeaken h (supRaw L P S)=supRaw L Q (naturalWeaken h '' S)

def InfRestriction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity)
    (τ : Ty) (D : Lower I τ) (L : LowerBounds D) (P Q : World I) (h : Extends P Q) (S : Set (Natural I τ D P)),
    rawWeaken h (infRaw L P S)=infRaw L Q (naturalWeaken h '' S)

end LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsTargets
