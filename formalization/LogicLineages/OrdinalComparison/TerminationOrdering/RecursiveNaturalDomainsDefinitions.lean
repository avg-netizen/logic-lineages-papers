module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalTupleLayerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomains
open Source Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer

def family {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) : Family I :=
  NaturalTupleLayerProof.layerFamily I τ (fun υ h => family I υ)
termination_by typeSize τ
decreasing_by exact h

def lower {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) : Lower I τ := fun υ _ => family I υ

/-- Definitional unfolding used only to transport the computed carrier. -/
theorem familyEquation {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) : family I τ=NaturalTupleLayerProof.layerFamily I τ (lower I τ) := by
  rw [family]
  rfl

abbrev Value {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) := (family I τ).carrier P

def layerView {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Value I τ P) : Natural I τ (lower I τ) P :=
  Eq.mp (congrArg (fun F : Family I => F.carrier P) (familyEquation I τ)) a

def layerFold {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) (a : Natural I τ (lower I τ) P) : Value I τ P :=
  Eq.mp (congrArg (fun F : Family I => F.carrier P) (familyEquation I τ).symm) a

def enumerateValues {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Finset (Value I τ P) := ((family I τ).finite P).elems

def weaken {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {P Q : World I} (h : Extends P Q) (a : Value I τ P) : Value I τ Q := (family I τ).restrict h a

abbrev FullTuple {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (s : Suffix τ) (P : World I) := Tuple (lower I τ) s P

def applyValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty}
    {P : World I} (a : Value I τ P) (s : Suffix τ) (v : FullTuple I τ s P) : Value I s.val.2 P :=
  (layerView I τ P a).val.2 ⟨P,fun _ hp => hp⟩ s v

def groundToBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} {P : World I} (a : Value I .ground P) : Bits I .ground P :=
  (layerView I .ground P a).val.1

def groundFromBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} {P : World I} (a : Bits I .ground P) : Value I .ground P :=
  layerFold I .ground P ⟨⟨a,fun _ s => nomatch s.property⟩,by
    constructor
    · intro Q s; cases s.property
    · intro Q R h s; cases s.property⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalDomains
