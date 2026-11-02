module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplication
open Source Source.SourceSpecialApplication Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

abbrev Values {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (types : List Ty) (P : World I) := (i : Fin types.length) → Value I (types.get i) P

def weakenValues {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {types : List Ty} {P Q : World I} (h : Extends P Q) (v : Values I types P) : Values I types Q :=
  fun i => RecursiveNaturalDomains.weaken h (v i)

def fullSuffix (types : List Ty) (τ : Ty) (hne : types ≠ []) : Suffix (arrows types τ) :=
  ⟨(types,τ),(Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration (arrows types τ) types τ).mpr ⟨hne,rfl⟩⟩

/-- Empty identity or exactly one table indexed by the complete nonempty list. -/
def applyFull {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P : World I} (types : List Ty) (τ : Ty) : Value I (arrows types τ) P → Values I types P → Value I τ P :=
  match types with
  | [] => fun a _ => a
  | σ::rest => fun a v => applyValue a (fullSuffix (σ::rest) τ (by simp)) v

def applyWith {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P : World I} {σ : Ty} (a : Value I σ P) (types : List Ty) (τ : Ty) (v : Values I types P)
    (h : σ=arrows types τ) : Value I τ P :=
  applyFull types τ (Eq.mp (congrArg (fun υ => Value I υ P) h) a) v

end LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplication
