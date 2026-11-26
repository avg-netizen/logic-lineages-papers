module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminal
open OrdinalComparison.LayeredComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (encodeGate bank)
open OriginalPrintedCircuitNumericRun (runCode Fits)
open OriginalPrintedCircuitNumericPlainTerminal (TestArgs Args namesFit boolCode packTerminal)
open OriginalPrintedCircuitSequential (Gate Topological)
open OriginalPrintedCircuitTerminal (observe)
open OriginalMixedTerminalTest (Test boundedNames)

/-- All original syntax names, including literal binders. The answer
still uses the checked local update and ordinary source shadowing. -/
def namesCode (code : Nat) : List Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then
    BaseTermPrograms.variablesCode (code / 5).unpair.1 ++
      BaseTermPrograms.variablesCode (code / 5).unpair.2
  else if code % 5 = 2 then namesCode (code / 5)
  else if code % 5 = 3 then namesCode (code / 5).unpair.1 ++ namesCode (code / 5).unpair.2
  else (code / 5).unpair.1 :: namesCode (code / 5).unpair.2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def boundedGuard (p : TestArgs) : Bool :=
  BoundedSourcePrograms.Code.test p.2 && namesFit (p.1,namesCode p.2)

def finishBounded (p : TestArgs) : Nat :=
  if boundedGuard p then boolCode (BoundedSourcePrograms.Code.answer p.1 p.2) else 0

noncomputable def observeBoundedCode (f : Nat → Nat) (p : Args) : Nat :=
  match runCode f p.1 with
  | .inl why => why
  | .inr final => finishBounded (final,p.2)

def ExactBoundedTerminalData : Prop :=
  Computable namesCode ∧ Computable finishBounded ∧
  (∀ p : SourceFormula, namesCode p.encode = boundedNames p) ∧
  (∀ (values : List Nat) (p : SourceFormula),
    boundedGuard (values,p.encode) = true ↔
      (Test.bounded p).Admitted ∧ ∀ n ∈ boundedNames p, n < values.length) ∧
  ∀ (values : List Nat) (p : SourceFormula),
    BoundedSourcePrograms.Code.answer values p.encode = (Test.bounded p).answer (bank values)

def ExactNumericBoundedTerminalRun : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (observeBoundedCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args) (why : Nat), runCode f p.1 = .inl why →
    observeBoundedCode f p = why) ∧
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (values : List Nat) (p : SourceFormula), Fits values known gates →
      (Test.bounded p).Admitted → (∀ n ∈ boundedNames p, n < values.length) →
      observeBoundedCode f ((values,gates.map encodeGate),p.encode) =
        packTerminal (observe f (bank values) gates (.bounded p))

def FullOriginalPrintedCircuitNumericBoundedTerminal : Prop :=
  ExactBoundedTerminalData ∧ ExactNumericBoundedTerminalRun

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminal
