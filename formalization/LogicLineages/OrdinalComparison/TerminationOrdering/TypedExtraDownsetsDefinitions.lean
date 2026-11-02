module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLatticesProof
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsets
open Source Source.SourceTypeSupport FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

def types {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) : Finset Ty :=
  typeSupport I.source ∪ typeSupport I.target
abbrev TypeIndex {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) := {τ : Ty // τ ∈ types I}
instance typeIndexFinite {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) : Fintype (TypeIndex I) :=
  Fintype.ofFinset (types I) (by intro τ; rfl)

abbrev Packed {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (P : World I) :=
  Σ τ : TypeIndex I, Value I τ.val P

def PackedLE {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (a b : Packed I P) : Prop :=
  if h : a.1=b.1 then Eq.mp (congrArg (fun τ : TypeIndex I => Value I τ.val P) h) a.2 ≤ b.2 else False

instance packedLEDecision {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (a b : Packed I P) : Decidable (PackedLE a b) :=
  inferInstanceAs (Decidable (if h : a.1=b.1 then Eq.mp (congrArg (fun τ : TypeIndex I => Value I τ.val P) h) a.2 ≤ b.2 else False))

def DownClosed {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P : World I}
    (E : Finset (Value I τ P)) : Prop := ∀ a ∈ E,∀ b : Value I τ P,b ≤ a → b ∈ E
instance downClosedDecision {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P : World I}
    (E : Finset (Value I τ P)) : Decidable (DownClosed E) :=
  inferInstanceAs (Decidable (∀ a ∈ E,∀ b : Value I τ P,b ≤ a → b ∈ E))

abbrev Down {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I) :=
  {E : Finset (Value I τ P) // DownClosed E}
instance downFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Fintype (Down I τ P) :=
  Fintype.ofFinset (Finset.univ.filter fun E : Finset (Value I τ P) => DownClosed E)
    (by intro E; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl)

/-- Fiberwise representation of a down-set in the literal typed disjoint union. -/
abbrev Extras {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) (P : World I) :=
  (τ : TypeIndex I) → Down I τ.val P
instance extrasFinite {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (P : World I) : Fintype (Extras I P) := inferInstanceAs (Fintype ((τ : TypeIndex I) → Down I τ.val P))

def contains {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (E : Extras I P) (a : Packed I P) : Prop := a.2 ∈ (E a.1).val

def PackedDownClosed {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I}
    (S : Set (Packed I P)) : Prop := ∀ a ∈ S,∀ b,PackedLE b a → b ∈ S

def enumerateExtras {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (P : World I) : Finset (Extras I P) := Finset.univ

def packedWeaken {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {P Q : World I}
    (h : Extends P Q) (a : Packed I P) : Packed I Q := ⟨a.1,RecursiveNaturalDomains.weaken h a.2⟩

/-- Actual finite downward closure of the image, not just its successful members. -/
def imageFiber {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P Q : World I}
    (h : Extends P Q) (E : Finset (Value I τ P)) : Finset (Value I τ Q) :=
  Finset.univ.filter fun b => ∃ a ∈ E,b ≤ RecursiveNaturalDomains.weaken h a

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedExtraDownsets
