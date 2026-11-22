module
public import LogicLineages.PermittedControl.OriginalMixedGateSequentialTargets
public import LogicLineages.PermittedControl.OriginalNaturalFieldGatesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitSequential
open ArbitraryHeadSharedWire (Valuation)
open FieldComparison (ClosedNaturalFieldResult)

/-- The explicit ordered grammar has the original signed affine and
arbitrary collapse constructors, plus fixed iterate, entry norm and count. -/
inductive Gate where
  | base (g : OriginalMixedGateSequential.Gate)
  | field (g : OriginalNaturalFieldGates.Gate)

inductive Failure where
  | rejectedBase
  | invalidField
  | missedField

def Gate.output : Gate → Nat
  | .base g => g.output
  | .field g => g.output

def Gate.references : Gate → List Nat
  | .base g => g.references
  | .field g => g.references

def Gate.graph (f : Nat → Nat) (θ : Valuation) : Gate → Prop
  | .base g => g.graph f θ
  | .field g => g.graph f θ

def baseResult : Option Nat → Except Failure Nat
  | none => .error .rejectedBase
  | some value => .ok value

def fieldResult : ClosedNaturalFieldResult → Except Failure Nat
  | none => .error .invalidField
  | some none => .error .missedField
  | some (some value) => .ok value

noncomputable def Gate.read (f : Nat → Nat) (θ : Valuation) : Gate → Except Failure Nat
  | .base g => baseResult (g.read f θ)
  | .field g => fieldResult (g.read f θ)

def Graphs (f : Nat → Nat) (θ : Valuation) (gates : List Gate) : Prop :=
  ∀ g ∈ gates, g.graph f θ

def Topological : List Nat → List Gate → Prop
  | _, [] => True
  | known, g :: gs => (∀ n ∈ g.references, n ∈ known) ∧ g.output ∉ known ∧
    Topological (g.output :: known) gs

def outputs (gates : List Gate) : List Nat := gates.map Gate.output

def LeavesExternal (gates : List Gate) (base final : Valuation) : Prop :=
  ∀ n : Nat, n ∉ outputs gates → final n = base n

/-- Only hits write an output. Either failure status stops immediately
and keeps its actual cause; no zero/default enters later gate reads. -/
noncomputable def run (f : Nat → Nat) (state : Valuation) :
    List Gate → Except Failure Valuation
  | [] => .ok state
  | g :: gs =>
      match g.read f state with
      | .error why => .error why
      | .ok value => run f (Function.update state g.output value) gs

def ExactCircuitGateReads : Prop :=
  (∀ (f : Nat → Nat) (g : Gate) (θ : Valuation),
    g.read f θ = .ok (θ g.output) ↔ g.graph f θ) ∧
  (∀ (f : Nat → Nat) (g : Gate) (base final : Valuation),
    (∀ n ∈ g.references, final n = base n) → g.read f final = g.read f base) ∧
  ∀ (f : Nat → Nat) (g : OriginalNaturalFieldGates.Gate) (θ : Valuation),
    ((Gate.field g).read f θ = .error .invalidField ↔ ¬ g.domain (θ g.source)) ∧
    ((Gate.field g).read f θ = .error .missedField ↔
      g.domain (θ g.source) ∧ ∀ v, ¬ g.value f (θ g.source) v)

def ExactPrintedCircuitRun : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ base final : Valuation,
      run f base gates = .ok final ↔ Graphs f final gates ∧ LeavesExternal gates base final

def ExactPrintedCircuitFailureAndUniqueness : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ base : Valuation,
      ((∃ reason : Failure, run f base gates = .error reason) ↔
        ¬ ∃ final : Valuation, Graphs f final gates ∧ LeavesExternal gates base final) ∧
      ((∃ final : Valuation, run f base gates = .ok final) ↔
        ∃! final : Valuation, Graphs f final gates ∧ LeavesExternal gates base final) ∧
      ∀ final : Valuation, run f base gates = .ok final → ∀ n ∈ known, final n = base n

def FullOriginalPrintedCircuitSequential : Prop :=
  ExactCircuitGateReads ∧ ExactPrintedCircuitRun ∧ ExactPrintedCircuitFailureAndUniqueness

end LogicLineages.PermittedControl.OriginalPrintedCircuitSequential
