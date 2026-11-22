module
public import LogicLineages.PermittedControl.OriginalMixedGateNormalizationTargets
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedTerminalTest
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees extend)
open OriginalMixedGateSequential (Gate Topological run LeavesExternal)
open OriginalMixedGateNormalization (collapseEntries normalized Holds)

inductive Test where
  | rows (p : NormalForm.Formula)
  | bounded (p : SourceFormula)

def Test.Admitted : Test → Prop
  | .rows p => PreparedProjection.PlainPreparedFormula p
  | .bounded p => BoundedSource.test p = true

def Test.eval (θ : Valuation) : Test → Prop
  | .rows p => p.eval θ
  | .bounded p => p.eval θ

def Test.atPolarity (p : Test) (positive : Bool) (θ : Valuation) : Prop :=
  if positive then p.eval θ else ¬ p.eval θ

/-- Keep every literal bounded-test name, including names of binders.
Only free ones are needed for valuation locality. -/
def boundedNames : SourceFormula → List Nat
  | .equal a b | .less a b => a.variables ++ b.variables
  | .negative p => boundedNames p
  | .conjunction p q => boundedNames p ++ boundedNames q
  | .existsNat i p => i :: boundedNames p

def Test.names : Test → List Nat
  | .rows p => p.variables
  | .bounded p => boundedNames p

def testCeiling (p : Test) : Nat := p.names.foldr max 0

def rowAnswer (θ : Valuation) : NormalForm.Formula → Bool
  | .truth => true
  | .falsity => false
  | .atom (.nonnegative r) => decide (0 ≤ NormalForm.rowValue r θ)
  | .atom (.divisible m r) => decide (NormalForm.rowValue r θ % ((m + 1 : Nat) : Int) = 0)
  | .negative p => !rowAnswer θ p
  | .conjunction p q => rowAnswer θ p && rowAnswer θ q
  | .disjunction p q => rowAnswer θ p || rowAnswer θ q

def Test.answer (θ : Valuation) : Test → Bool
  | .rows p => rowAnswer θ p
  | .bounded p => BoundedSource.answer θ p

noncomputable def observe (f : Nat → Nat) (base : Valuation) (gates : List Gate) (p : Test) : Option Bool :=
  (run f base gates).map (fun final => p.answer final)

def ExactTerminalTestRead : Prop :=
  ∀ (p : Test), p.Admitted → ∀ (θ : Valuation) (positive : Bool),
    p.answer θ = positive ↔ p.atPolarity positive θ

def ExactProtectedTestLift : Prop :=
  ∀ (gates : List Gate) (p : Test) (original : Valuation),
    let lifted := extend original (collapseEntries (testCeiling p) gates)
    (∀ name ∈ p.names, lifted name = original name) ∧
    (p.eval lifted ↔ p.eval original) ∧
    (p.Admitted → p.answer lifted = p.answer original)

/-- Even when the test is false, the normalized computational graph
must still be a positive actual graph with the original external ties. -/
def ExactObservedMixedTerminal : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate), Topological known gates →
    ∀ (base : Valuation) (p : Test), p.Admitted →
      ((observe f base gates p = none) ↔ run f base gates = none) ∧
      ∀ positive : Bool,
        observe f base gates p = some positive ↔
          ∃ original lifted : Valuation, LeavesExternal gates base original ∧
            Holds f lifted (normalized (testCeiling p) gates) ∧
            Agrees (collapseEntries (testCeiling p) gates) original lifted ∧ p.atPolarity positive lifted

def FullOriginalMixedTerminalTest : Prop :=
  ExactTerminalTestRead ∧ ExactProtectedTestLift ∧ ExactObservedMixedTerminal

end LogicLineages.PermittedControl.OriginalMixedTerminalTest
