module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets TypedExtraAppend

def MembershipCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E : Extras I P) (xs : List (Packed I P)) (a : Packed I P),
    a.2 ∈ appendRaw E xs a.1 ↔ contains E a ∨ ∃ p ∈ xs,PackedLE a p

def DownwardClosure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E : Extras I P) (xs : List (Packed I P)) (τ : TypeIndex I),DownClosed (appendRaw E xs τ)

def EmptyIdentity : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E : Extras I P) (τ : TypeIndex I),appendRaw E [] τ=(E τ).val

def SuppliedIncluded : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E : Extras I P) (xs : List (Packed I P)) (p : Packed I P),
    p ∈ xs → p.2 ∈ appendRaw E xs p.1

def AppendMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E F : Extras I P) (xs ys : List (Packed I P)),
    E ≤ F → Dominated xs ys → ∀ τ,appendRaw E xs τ ⊆ appendRaw F ys τ

def LeastClosure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P : World I) (E F : Extras I P) (xs : List (Packed I P)),
    E ≤ F → (∀ p ∈ xs,contains F p) → ∀ τ,appendRaw E xs τ ⊆ (F τ).val

def RestrictionAppend : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (I : Input Symbol arity) (P Q : World I) (h : Extends P Q) (E : Extras I P) (xs : List (Packed I P)) (τ : TypeIndex I),
    imageFiber h (appendRaw E xs τ)=
      appendRaw ((TypedExtraDownsetsProof.extrasFamily I).restrict h E) (xs.map (packedWeaken h)) τ

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraAppendTargets
