module
public import LogicLineages.PermittedControl.OriginalMixedGateSequentialTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedGateNormalization
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadFreshWireAllocation (Wire install attach)
open ArbitraryHeadWireList (NormalGate normalizeGate Agrees Fresh extend hiddenNames)
open OriginalMixedGateSequential (Gate Graphs Topological LeavesExternal run)

def collapseWire : Gate → Option Wire
  | .affine .. => none
  | .collapse w => some w

def collapseWires (gates : List Gate) : List Wire := gates.filterMap collapseWire

def listedNames (gates : List Gate) : List Nat :=
  gates.map Gate.output ++ gates.flatMap Gate.references

/-- Extra caller-protected names (e.g. output test and externally supplied
names) can be protected by supplying any numeric ceiling for them. -/
def protectedCeiling (exteriorCeiling : Nat) (gates : List Gate) : Nat :=
  (listedNames gates).foldr max exteriorCeiling

def firstHidden (exteriorCeiling : Nat) (gates : List Gate) : Nat :=
  protectedCeiling exteriorCeiling gates + 1

def collapseEntries (exteriorCeiling : Nat) (gates : List Gate) : List ArbitraryHeadWireList.Gate :=
  attach (firstHidden exteriorCeiling gates) (collapseWires gates)

/-- Original affine syntax stays literal and in place. Only an original
collapse uses the arbitrary-head finite/limit wire rewrite. Candidate
names advance in original collapse occurrence order; finite heads use
no hidden name. -/
def normalizeFrom : Nat → List Gate → List NormalGate
  | _, [] => []
  | n, .affine e out :: gs => .affine e out :: normalizeFrom n gs
  | n, .collapse w :: gs => normalizeGate (install w n) :: normalizeFrom (n+1) gs

def normalized (exteriorCeiling : Nat) (gates : List Gate) : List NormalGate :=
  normalizeFrom (firstHidden exteriorCeiling gates) gates

def Holds (f : Nat → Nat) (θ : Valuation) (gates : List NormalGate) : Prop :=
  ∀ g ∈ gates, g.Holds f θ

def AffinesAt (θ : Valuation) : List Gate → Prop
  | [] => True
  | .affine e out :: gs => (NaturalAffineGateGraph.graph out e).eval θ ∧ AffinesAt θ gs
  | .collapse _ :: gs => AffinesAt θ gs

def ExactMixedFreshAliases : Prop :=
  ∀ (exteriorCeiling : Nat) (gates : List Gate),
    exteriorCeiling ≤ protectedCeiling exteriorCeiling gates ∧
    (∀ g ∈ gates, g.output ≤ protectedCeiling exteriorCeiling gates ∧
      ∀ n ∈ g.references, n ≤ protectedCeiling exteriorCeiling gates) ∧
    Fresh (collapseEntries exteriorCeiling gates) ∧
    ∀ n ∈ hiddenNames (collapseEntries exteriorCeiling gates),
      protectedCeiling exteriorCeiling gates < n

def ExactMixedNormalizedExtension : Prop :=
  ∀ (f : Nat → Nat) (exteriorCeiling : Nat) (gates : List Gate) (ν : Valuation),
    let entries := collapseEntries exteriorCeiling gates
    let norm := normalized exteriorCeiling gates
    (∀ θ : Valuation,
      (Holds f θ norm ∧ Agrees entries ν θ) ↔ Graphs f ν gates ∧ θ = extend ν entries) ∧
    ((∃! θ : Valuation, Holds f θ norm ∧ Agrees entries ν θ) ↔ Graphs f ν gates) ∧
    (∀ n : Nat, n ≤ protectedCeiling exteriorCeiling gates → extend ν entries n = ν n)

def ExactMixedRunThenNormalize : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (exteriorCeiling : Nat) (base final : Valuation),
      run f base gates = some final ↔ LeavesExternal gates base final ∧
        ∃! lifted : Valuation, Holds f lifted (normalized exteriorCeiling gates) ∧
          Agrees (collapseEntries exteriorCeiling gates) final lifted

def FullOriginalMixedGateNormalization : Prop :=
  ExactMixedFreshAliases ∧ ExactMixedNormalizedExtension ∧ ExactMixedRunThenNormalize

end LogicLineages.PermittedControl.OriginalMixedGateNormalization
