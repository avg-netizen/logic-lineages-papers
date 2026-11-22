module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunTargets
public import LogicLineages.PermittedControl.OriginalPrintedCircuitTerminalTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (bank encodeGate packResult)
open OriginalPrintedCircuitNumericRun (runCode Fits)
open OriginalPrintedCircuitSequential (Gate Failure Topological)
open OriginalPrintedCircuitTerminal (observe)
open OriginalMixedTerminalTest (Test)

abbrev TestArgs := List Nat × Nat
abbrev Args := OriginalPrintedCircuitNumericRun.Args × Nat

def namesFit (p : List Nat × List Nat) : Bool :=
  p.2.all (fun name => decide (name < p.1.length))

/-- Genuinely variable-only, not the wider existing plain-phi test.
Every original occurrence is read, even with signed zero coefficient. -/
def atomVariablesOnly (payload : Nat) : Bool :=
  (LinearRows.Code.decodeAtom payload).2.2.2.all (fun term => decide (term.2.1 = 0))

def variablesOnly (code : Nat) : Bool := (LinearRows.Code.atoms code).all atomVariablesOnly

def plainGuard (p : TestArgs) : Bool :=
  variablesOnly p.2 && namesFit (p.1,MaximalPlainBranchPrograms.Code.variables p.2)

def plainAnswer (p : TestArgs) : Bool :=
  ZeroValuation.Code.evaluate
    ((MaximalPlainBranchPrograms.Code.variables p.2).foldr
      (fun name residual => BoundedRows.Code.formula name (bank p.1 name) residual) p.2)

def boolCode (b : Bool) : Nat := if b then 5 else 4

def packTerminal : Except Failure Bool → Nat
  | .error why => packResult (.error why)
  | .ok b => boolCode b

def finishPlain (p : TestArgs) : Nat := if plainGuard p then boolCode (plainAnswer p) else 0

noncomputable def observePlainCode (f : Nat → Nat) (p : Args) : Nat :=
  match runCode f p.1 with
  | .inl why => why
  | .inr final => finishPlain (final,p.2)

def ExactPlainTerminalData : Prop :=
  Primrec namesFit ∧ Primrec plainGuard ∧ Primrec plainAnswer ∧
  (∀ (values : List Nat) (p : NormalForm.Formula),
    plainGuard (values,p.encode) = true ↔
      (Test.rows p).Admitted ∧ ∀ n ∈ p.variables, n < values.length) ∧
  ∀ (values : List Nat) (p : NormalForm.Formula), (Test.rows p).Admitted →
    plainAnswer (values,p.encode) = (Test.rows p).answer (bank values)

def ExactNumericPlainTerminalRun : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (observePlainCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args) (why : Nat), runCode f p.1 = .inl why →
    observePlainCode f p = why) ∧
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (values : List Nat) (p : NormalForm.Formula), Fits values known gates →
      (Test.rows p).Admitted → (∀ n ∈ p.variables, n < values.length) →
      observePlainCode f ((values,gates.map encodeGate),p.encode) =
        packTerminal (observe f (bank values) gates (.rows p))

def FullOriginalPrintedCircuitNumericPlainTerminal : Prop :=
  ExactPlainTerminalData ∧ ExactNumericPlainTerminalRun

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
