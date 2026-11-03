module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCodingProof
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Order

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBits
open Source Source.SourceTypeSupport Source.SourcePortContexts Source.SourceOpenedObservations

structure Input (Symbol : Type) (arity : Symbol → Nat) where
  context : List Ty
  sourceType : Ty
  targetType : Ty
  source : Term Symbol arity context sourceType
  target : Term Symbol arity context targetType

def budget {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) := lambdaDepth I.target

def worldList {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) : List (PortContext (budget I)) :=
  portContexts (budget I) (literalTypes I.source++literalTypes I.target)

abbrev World {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) :=
  {P : PortContext (budget I) // P ∈ worldList I}

instance worldFintype {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) : Fintype (World I) :=
  Fintype.ofFinset (worldList I).toFinset (by intro P; exact List.mem_toFinset)

/-- Typed slot inclusion. No invariant about a semantic value is a guard. -/
def Extends {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (P Q : World I) : Prop :=
  ∀ p ∈ P.val,p ∈ Q.val

instance extendsDecidable {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (P Q : World I) : Decidable (Extends P Q) :=
  inferInstanceAs (Decidable (∀ p ∈ P.val,p ∈ Q.val))

abbrev Future {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (P : World I) :=
  {Q : World I // Extends P Q}

instance futureFintype {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (P : World I) : Fintype (Future P) :=
  Fintype.ofFinset (Finset.univ.filter fun Q : World I => Extends P Q)
    (by intro Q; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl)

instance observationDecidableEq {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Γ : List Ty} {B : Nat} :
    DecidableEq (Observation Symbol arity Γ B) := SourceObservationCodingProof.observationDecidableEq

abbrev ObservationAt {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I) :=
  {o : Observation Symbol arity I.context (budget I) //
    o ∈ observations (budget I) I.target ∧ o.ports=P.val ∧ o.resultType=τ}

instance observationAtFintype {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Fintype (ObservationAt I τ P) :=
  Fintype.ofFinset ((observations (budget I) I.target).toFinset.filter fun o => o.ports=P.val ∧ o.resultType=τ)
    (by intro o; simp only [Finset.mem_filter,List.mem_toFinset]; rfl)

/-- One availability bit and two actual-observation characteristic functions. -/
abbrev LocalBits {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I) :=
  Bool × (ObservationAt I τ P → Bool) × (ObservationAt I τ P → Bool)

/-- Components at every actual extension, not only the current world. -/
abbrev Bits {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I) :=
  (Q : Future P) → LocalBits I τ Q.val

instance bitsFintype {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Fintype (Bits I τ P) := inferInstanceAs (Fintype ((Q : Future P) → LocalBits I τ Q.val))

noncomputable instance bitsCompleteLattice {Symbol : Type} {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : CompleteLattice (Bits I τ P) := inferInstanceAs (CompleteLattice ((Q : Future P) → LocalBits I τ Q.val))

/-- Executable exhaustive enumeration; equality is literal, not list-position identity. -/
def enumerateBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Finset (Bits I τ P) := Finset.univ

def weaken {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {P Q : World I} (h : Extends P Q) (a : Bits I τ P) : Bits I τ Q :=
  fun R => a ⟨R.val,fun p hp => R.property p (h p hp)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteObservationBits
