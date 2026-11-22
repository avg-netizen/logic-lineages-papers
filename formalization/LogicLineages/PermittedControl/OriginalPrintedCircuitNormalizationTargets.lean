module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialTargets
public import LogicLineages.PermittedControl.OriginalMixedGateNormalizationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadFreshWireAllocation (install)
open ArbitraryHeadWireList (NormalGate normalizeGate hiddenNames Agrees extend)
open OriginalPrintedCircuitSequential (Gate Topological Graphs run LeavesExternal)

inductive NormalizedGate where
  | base (g : NormalGate)
  | field (g : OriginalNaturalFieldGates.Gate)

def baseGate : Gate → Option OriginalMixedGateSequential.Gate
  | .base g => some g
  | .field _ => none

def baseGates (gates : List Gate) : List OriginalMixedGateSequential.Gate := gates.filterMap baseGate

def names (gates : List Gate) : List Nat :=
  gates.map Gate.output ++ gates.flatMap Gate.references

/-- The original field inputs, affine references, all outputs and the
explicit extra exterior/test names covered by the supplied ceiling. -/
def protectedCeiling (ext : Nat) (gates : List Gate) : Nat := (names gates).foldr max ext

def entries (ext : Nat) (gates : List Gate) : List ArbitraryHeadWireList.Gate :=
  OriginalMixedGateNormalization.collapseEntries (protectedCeiling ext gates) (baseGates gates)

def firstHidden (ext : Nat) (gates : List Gate) : Nat :=
  OriginalMixedGateNormalization.firstHidden (protectedCeiling ext gates) (baseGates gates)

def normalizeFrom : Nat → List Gate → List NormalizedGate
  | _, [] => []
  | n, .base (.affine e out) :: gs => .base (.affine e out) :: normalizeFrom n gs
  | n, .base (.collapse w) :: gs => .base (normalizeGate (install w n)) :: normalizeFrom (n+1) gs
  | n, .field field :: gs => .field field :: normalizeFrom n gs

def normalized (ext : Nat) (gates : List Gate) : List NormalizedGate :=
  normalizeFrom (firstHidden ext gates) gates

def NormalizedGate.graph (f : Nat → Nat) (θ : Valuation) : NormalizedGate → Prop
  | .base g => g.Holds f θ
  | .field g => g.graph f θ

def Holds (f : Nat → Nat) (θ : Valuation) (gs : List NormalizedGate) : Prop :=
  ∀ g ∈ gs, g.graph f θ

def FieldsAt (f : Nat → Nat) (θ : Valuation) : List Gate → Prop
  | [] => True
  | .base _ :: gs => FieldsAt f θ gs
  | .field g :: gs => g.graph f θ ∧ FieldsAt f θ gs

def ExactPrintedProtection : Prop :=
  ∀ (ext : Nat) (gates : List Gate),
    ext ≤ protectedCeiling ext gates ∧
    (∀ g ∈ gates, g.output ≤ protectedCeiling ext gates ∧
      ∀ n ∈ g.references, n ≤ protectedCeiling ext gates) ∧
    ∀ n ∈ hiddenNames (entries ext gates), protectedCeiling ext gates < n

def ExactPrintedNormalizedExtension : Prop :=
  ∀ (f : Nat → Nat) (ext : Nat) (gates : List Gate) (ν : Valuation),
    (∀ θ : Valuation,
      (Holds f θ (normalized ext gates) ∧ Agrees (entries ext gates) ν θ) ↔
        Graphs f ν gates ∧ θ = extend ν (entries ext gates)) ∧
    ((∃! θ : Valuation, Holds f θ (normalized ext gates) ∧ Agrees (entries ext gates) ν θ) ↔
      Graphs f ν gates) ∧
    (∀ n : Nat, n ≤ protectedCeiling ext gates → extend ν (entries ext gates) n = ν n)

def ExactPrintedRunThenNormalize : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (ext : Nat) (base final : Valuation),
      run f base gates = .ok final ↔ LeavesExternal gates base final ∧
        ∃! lifted : Valuation, Holds f lifted (normalized ext gates) ∧ Agrees (entries ext gates) final lifted

def FullOriginalPrintedCircuitNormalization : Prop :=
  ExactPrintedProtection ∧ ExactPrintedNormalizedExtension ∧ ExactPrintedRunThenNormalize

end LogicLineages.PermittedControl.OriginalPrintedCircuitNormalization
