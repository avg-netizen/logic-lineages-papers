module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraph
open NormalForm

def nonnegative (row : NormalForm.Row) : NormalForm.Formula := .atom (.nonnegative row)
def equation := SourceTermGraph.equation

def multiplyRow (z x c : Nat) : NormalForm.Row :=
  (0, [(1, .variable z), (-(c : Int), .variable x)])
def subtraction (z x y : Nat) : NormalForm.Formula :=
  .disjunction
    (.conjunction (nonnegative (0, [(1, .variable y), (-1, .variable x)]))
      (equation (0, [(1, .variable z)])))
    (.conjunction (nonnegative (-1, [(1, .variable x), (-1, .variable y)]))
      (equation (0, [(1, .variable x), (-1, .variable y), (-1, .variable z)])))
def division (z x c : Nat) : NormalForm.Formula :=
  if c = 0 then equation (0, [(1, .variable z)]) else
    .conjunction
      (nonnegative (0, [(1, .variable x), (-(c : Int), .variable z)]))
      (nonnegative ((c : Int) - 1, [(c, .variable z), (-1, .variable x)]))

/-- The two fresh names are u and z. Phi(z) and Phi(u) are already literal
normal-form summands, so their values require no independent aliases. -/
def inverse (u z x : Nat) : NormalForm.Formula :=
  .conjunction (equation (-1, [(1, .variable u), (-1, .variable z)]))
    (.conjunction
      (.disjunction (equation (0, [(1, .variable z)]))
        (nonnegative (0, [(1, .variable x), (-1, .phi z 0)])))
      (nonnegative (-1, [(1, .phi u 0), (-1, .variable x)])))

def nodeCount : Term → Nat
  | .numeral _ | .variable _ => 1
  | .add a b | .subtract a b => nodeCount a + nodeCount b + 1
  | .phiInverse a => nodeCount a + 2
  | .multiply _ a | .divide _ a | .phi a | .hyper a | .hyperInverse a => nodeCount a + 1
def allocated (start : Nat) (t : Term) : List Nat := SourceTermGraph.names start (nodeCount t)
def output (start : Nat) (t : Term) : Nat := start + nodeCount t - 1
def Fresh (start : Nat) (t : Term) : Prop := ∀ i ∈ t.variables, i < start

/-- Concrete postorder functional graph. Unsupported H syntax is explicit
falsity; every semantic target below retains the actual H-free test. -/
def graph (start : Nat) : Term → NormalForm.Formula
  | .numeral n => equation (SourceTermGraph.numeralRow start n)
  | .variable i => equation (SourceTermGraph.variableRow start i)
  | .add a b =>
      .conjunction (graph start a) (.conjunction (graph (start + nodeCount a) b)
        (equation (SourceTermGraph.additionRow (output start (.add a b))
          (output start a) (output (start + nodeCount a) b))))
  | .subtract a b =>
      .conjunction (graph start a) (.conjunction (graph (start + nodeCount a) b)
        (subtraction (output start (.subtract a b)) (output start a)
          (output (start + nodeCount a) b)))
  | .multiply c a => .conjunction (graph start a)
      (equation (multiplyRow (output start (.multiply c a)) (output start a) c))
  | .divide c a => .conjunction (graph start a)
      (division (output start (.divide c a)) (output start a) c)
  | .phi a => .conjunction (graph start a)
      (equation (SourceTermGraph.phiRow (output start (.phi a)) (output start a)))
  | .phiInverse a => .conjunction (graph start a)
      (inverse (start + nodeCount a) (output start (.phiInverse a)) (output start a))
  | .hyper _ | .hyperInverse _ => .falsity

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraph
