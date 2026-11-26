module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
open ArbitraryHeadSharedWire (Valuation)
open OriginalPrintedCircuitSequential (Gate Failure Topological run)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate bank readCode packResult)

abbrev State := Nat ⊕ List Nat
abbrev Args := List Nat × List RawGate
abbrev StepArgs := List Nat × RawGate

def rawOutput (g : RawGate) : Nat := g.2.2.1

def install (p : List Nat × Nat × Nat) : State :=
  if p.2.2 < 4 then .inl p.2.2
  else .inr (p.1.set p.2.1 (p.2.2 - 4))

/-- Output capacity is an additional raw check; code zero is the
existing parser/capacity rejection, not a semantic gate result. -/
noncomputable def step (f : Nat → Nat) (p : StepArgs) : State :=
  if rawOutput p.2 < p.1.length then install (p.1,rawOutput p.2,readCode f p)
  else .inl 0

noncomputable def stepCarry (f : Nat → Nat) : State × RawGate → State
  | (.inl why, _) => .inl why
  | (.inr values, g) => step f (values,g)

noncomputable def runCode (f : Nat → Nat) (p : Args) : State :=
  p.2.foldl (fun state g => stepCarry f (state,g)) (.inr p.1)

def EncodesRun (size : Nat) : State → Except Failure Valuation → Prop
  | .inl code, .error why => code = packResult (.error why)
  | .inr values, .ok final => values.length = size ∧ bank values = final
  | _, _ => False

def Fits (values : List Nat) (known : List Nat) (gates : List Gate) : Prop :=
  (∀ n ∈ known, n < values.length) ∧ ∀ g ∈ gates, g.output < values.length

def ExactNumericBankUpdates : Prop :=
  (∀ (values : List Nat) (i v : Nat), (values.set i v).length = values.length) ∧
  ∀ (values : List Nat) (i v : Nat), i < values.length →
    bank (values.set i v) = Function.update (bank values) i v

def ExactNumericRunBehavior : Prop :=
  (∀ (f : Nat → Nat) (values : List Nat) (g : RawGate), values.length ≤ rawOutput g →
    step f (values,g) = .inl 0) ∧
  ∀ (f : Nat → Nat) (values : List Nat) (prefix suffix : List RawGate) (why : Nat),
    runCode f (values,prefix) = .inl why → runCode f (values,prefix ++ suffix) = .inl why

def ExactNumericTypedRun : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ values : List Nat, Fits values known gates →
      EncodesRun values.length (runCode f (values,gates.map encodeGate)) (run f (bank values) gates)

def FullOriginalPrintedCircuitNumericRun : Prop :=
  ExactNumericBankUpdates ∧ ExactNumericRunBehavior ∧ ExactNumericTypedRun ∧
  ∀ f : Nat → Nat, Computable f → Computable (runCode f)

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
