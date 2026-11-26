import LogicLineages.PersistentMarking.Comparison
namespace LogicLineages.PersistentMarking.ComparisonTargets
open Spine

def FixedRankedArity : Prop := ∀ S name a b,
  Admitted S (.ranked name a) → Admitted S (.ranked name b) → a = b

def NativeEquivalent : Prop := ∀ S σ τ,
  Equivalent S (.case σ) (.recursor τ)

def NativeAboveApplication : Prop := ∀ S σ τ,
  Precedes S .succ (.app σ τ)

def RankedAboveNative : Prop := ∀ S name arity σ,
  Admitted S (.ranked name arity) → Precedes S (.ranked name arity) (.case σ)

def RemoveLength : Prop := ∀ xs x ys, Remove xs x ys → xs.length = ys.length+1

def SplitLength : Prop := ∀ xs ys zs, Split xs ys zs → xs.length = ys.length+zs.length

def WeakTargetsOrdinary : Prop := ∀ S q t, Weak S q t → Ordinary t

def StrictTargetsOrdinary : Prop := ∀ S q t, Strict S q t → Ordinary t

def StrictIncluded : Prop := ∀ S q t, Strict S q t → Weak S q t

def OrdinaryReflexive : Prop := ∀ S q σ,
  PaperTerm S q σ → Ordinary q → Weak S q q

end LogicLineages.PersistentMarking.ComparisonTargets
