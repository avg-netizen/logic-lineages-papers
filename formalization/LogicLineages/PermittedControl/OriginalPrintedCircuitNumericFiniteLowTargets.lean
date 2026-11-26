module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalTargets
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminalTargets
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate bank)
open OriginalPrintedCircuitNumericRun (Fits runCode)
open OriginalPrintedCircuitNumericPlainTerminal (finishPlain boolCode packTerminal)
open OriginalPrintedCircuitNumericBoundedTerminal (finishBounded)
open OriginalPrintedCircuitSequential (Gate Topological LeavesExternal)
open OriginalPrintedCircuitTerminal (observe)
open OriginalPrintedCircuitNormalization (entries normalized Holds)
open OriginalPrintedCircuitNormalizedTerminal (exterior)
open OriginalMixedTerminalTest (Test)

abbrev RawTest := Nat × Nat
abbrev EvalArgs := List Nat × List RawGate × RawTest
abbrev LowArgs := Nat × Nat × EvalArgs
abbrev Row := Nat × Nat

def encodeTest : Test → RawTest
  | .rows p => (0,p.encode)
  | .bounded p => (1,p.encode)

def finish (p : List Nat × RawTest) : Nat :=
  if p.2.1 = 0 then finishPlain (p.1,p.2.2)
  else if p.2.1 = 1 then finishBounded (p.1,p.2.2)
  else 0

noncomputable def observeCode (f : Nat → Nat) (p : EvalArgs) : Nat :=
  match runCode f (p.1,p.2.1) with
  | .inl why => why
  | .inr values => finish (values,p.2.2)

noncomputable def lowPoint (f : Nat → Nat) (p : LowArgs) (a : Nat) : Nat :=
  if p.1 < p.2.2.1.length then
    observeCode f (p.2.2.1.set p.1 a,p.2.2.2.1,p.2.2.2.2)
  else 0

noncomputable def lowTable (f : Nat → Nat) (p : LowArgs) : List Row :=
  (List.range p.2.1).map (fun a => (a,lowPoint f p a))

def hasRows (p : Bool × List Row) : Bool :=
  p.2.any (fun r => decide (r.2 = boolCode p.1))

noncomputable def anyPolarity (f : Nat → Nat) (p : LowArgs × Bool) : Bool :=
  hasRows (p.2,lowTable f p.1)

def typedArgs (values : List Nat) (gates : List Gate) (rank bound : Nat) (p : Test) : LowArgs :=
  (rank,bound,values,gates.map encodeGate,encodeTest p)

def LiftedAt (f : Nat → Nat) (known : List Nat) (gates : List Gate)
    (base : Valuation) (p : Test) (positive : Bool) : Prop :=
  ∃ original lifted : Valuation, LeavesExternal gates base original ∧
    Holds f lifted (normalized (exterior known p) gates) ∧
    Agrees (entries (exterior known p) gates) original lifted ∧
    (∀ n ∈ known, lifted n = base n) ∧ p.atPolarity positive lifted

def ExactUnifiedNumericTerminal : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (observeCode f)) ∧
  (∀ (f : Nat → Nat) (p : EvalArgs) (why : Nat),
    runCode f (p.1,p.2.1) = .inl why → observeCode f p = why) ∧
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (values : List Nat) (p : Test), Fits values known gates →
      p.Admitted → (∀ n ∈ p.names, n < values.length) →
      observeCode f (values,gates.map encodeGate,encodeTest p) =
        packTerminal (observe f (bank values) gates p)

def ExactNumericFiniteLowLayout : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (lowTable f) ∧ Computable (anyPolarity f)) ∧
  ∀ (f : Nat → Nat) (p : LowArgs),
    (lowTable f p).map Prod.fst = List.range p.2.1 ∧
    ∀ a code : Nat, (a,code) ∈ lowTable f p ↔ a < p.2.1 ∧ code = lowPoint f p a

def ExactNumericPrintedFiniteLow : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (values : List Nat) (rank bound : Nat) (p : Test), Fits values known gates →
      rank ∈ known → p.Admitted → (∀ n ∈ p.names, n < values.length) →
      let args := typedArgs values gates rank bound p
      (∀ a : Nat, lowPoint f args a =
        packTerminal (observe f (Function.update (bank values) rank a) gates p)) ∧
      (∀ (a : Nat) (positive : Bool), (a,boolCode positive) ∈ lowTable f args ↔
        a < bound ∧ LiftedAt f known gates (Function.update (bank values) rank a) p positive) ∧
      ∀ positive : Bool, anyPolarity f (args,positive) = true ↔
        ∃ a < bound, LiftedAt f known gates (Function.update (bank values) rank a) p positive

def FullOriginalPrintedCircuitNumericFiniteLow : Prop :=
  ExactUnifiedNumericTerminal ∧ ExactNumericFiniteLowLayout ∧ ExactNumericPrintedFiniteLow

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
