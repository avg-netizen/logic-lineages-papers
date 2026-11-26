module
public import LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedGateSequential
open OrdinalComparison
open ArbitraryHeadSharedWire (Valuation headCode originalGraph)
open ArbitraryHeadFreshWireAllocation (Wire)
open NaturalAffineGateGraph (Expression)

/-- Only these two original gate constructors are claimed. Affine
expressions keep all signed occurrences, including repetitions. -/
inductive Gate where
  | affine (e : Expression) (output : Nat)
  | collapse (w : Wire)

def Gate.output : Gate → Nat
  | .affine _ n => n
  | .collapse w => w.output

def Gate.references : Gate → List Nat
  | .affine e _ => e.2.map Prod.snd
  | .collapse w => [w.source]

def Gate.graph (f : Nat → Nat) (θ : Valuation) : Gate → Prop
  | .affine e n => (NaturalAffineGateGraph.graph n e).eval θ
  | .collapse w => originalGraph f w.head w.source w.output θ

noncomputable def Gate.read (f : Nat → Nat) (θ : Valuation) : Gate → Option Nat
  | .affine e _ =>
      let s := NaturalAffineGateGraph.signedValue e θ
      if 0 ≤ s then some s.toNat else none
  | .collapse w => ArbitraryHeadSequentialOutputs.reader f w θ

def Graphs (f : Nat → Nat) (θ : Valuation) (gates : List Gate) : Prop :=
  ∀ gate ∈ gates, gate.graph f θ

def Topological : List Nat → List Gate → Prop
  | _, [] => True
  | known, g :: gs => (∀ n ∈ g.references, n ∈ known) ∧ g.output ∉ known ∧
      Topological (g.output :: known) gs

def outputs (gates : List Gate) : List Nat := gates.map Gate.output

def LeavesExternal (gates : List Gate) (base final : Valuation) : Prop :=
  ∀ n : Nat, n ∉ outputs gates → final n = base n

noncomputable def run (f : Nat → Nat) (state : Valuation) : List Gate → Option Valuation
  | [] => some state
  | g :: gs =>
      match g.read f state with
      | none => none
      | some value => run f (Function.update state g.output value) gs

def ExactMixedGateRead : Prop :=
  (∀ (f : Nat → Nat) (θ : Valuation) (g : Gate),
    g.read f θ = some (θ g.output) ↔ g.graph f θ) ∧
  ∀ (f : Nat → Nat) (θ : Valuation) (e : Expression) (out : Nat),
    (Gate.affine e out).read f θ = none ↔ NaturalAffineGateGraph.signedValue e θ < 0

def ExactMixedSequential : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ base final : Valuation,
      run f base gates = some final ↔ Graphs f final gates ∧ LeavesExternal gates base final

def ExactMixedFailureAndUniqueness : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ base : Valuation,
      (run f base gates = none ↔
        ¬ ∃ final : Valuation, Graphs f final gates ∧ LeavesExternal gates base final) ∧
      (run f base gates ≠ none ↔
        ∃! final : Valuation, Graphs f final gates ∧ LeavesExternal gates base final) ∧
      ∀ final : Valuation, run f base gates = some final → ∀ n ∈ known, final n = base n

def FullOriginalMixedGateSequential : Prop :=
  ExactMixedGateRead ∧ ExactMixedSequential ∧ ExactMixedFailureAndUniqueness

end LogicLineages.PermittedControl.OriginalMixedGateSequential
