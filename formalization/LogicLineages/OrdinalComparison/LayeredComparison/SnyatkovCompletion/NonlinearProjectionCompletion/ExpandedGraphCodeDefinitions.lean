module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCode

abbrev RowData := NormalForm.Code.RowData

/-- The unchanged radix-ten occurrence count. Phi inverse allocates two
names; the unsupported H constructors still count their child and one name. -/
def nodeCount (code : Nat) : Nat :=
  if code % 10 = 0 then 1
  else if code % 10 = 1 then 1
  else if code % 10 = 2 then
    nodeCount (code / 10).unpair.1 + nodeCount (code / 10).unpair.2 + 1
  else if code % 10 = 3 then
    nodeCount (code / 10).unpair.1 + nodeCount (code / 10).unpair.2 + 1
  else if code % 10 = 4 then nodeCount (code / 10).unpair.2 + 1
  else if code % 10 = 5 then nodeCount (code / 10).unpair.2 + 1
  else if code % 10 = 8 then nodeCount (code / 10) + 2
  else nodeCount (code / 10) + 1
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 10 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 10)
    have hr := Nat.unpair_right_le (code / 10)
    omega

/-- Literal original contiguous allocation order and saturated output name. -/
def allocated (start code : Nat) : List Nat := SourceTermGraph.names start (nodeCount code)
def output (start code : Nat) : Nat := start + nodeCount code - 1

def disjunction (a b : Nat) : Nat := 6 * Nat.pair a b + 5

def multiplyRow (z x c : Nat) : RowData :=
  (0, [(1, SourceTermGraph.Code.variableData z), (-(c : Int), SourceTermGraph.Code.variableData x)])

def subtraction (z x y : Nat) : Nat :=
  disjunction
    (SourceTermGraph.Code.conjunction
      (SourceTermGraph.Code.atom (0, [(1, SourceTermGraph.Code.variableData y), (-1, SourceTermGraph.Code.variableData x)]))
      (SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData z)])))
    (SourceTermGraph.Code.conjunction
      (SourceTermGraph.Code.atom (-1, [(1, SourceTermGraph.Code.variableData x), (-1, SourceTermGraph.Code.variableData y)]))
      (SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData x), (-1, SourceTermGraph.Code.variableData y), (-1, SourceTermGraph.Code.variableData z)])))

def division (z x c : Nat) : Nat :=
  if c = 0 then SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData z)]) else
    SourceTermGraph.Code.conjunction
      (SourceTermGraph.Code.atom (0, [(1, SourceTermGraph.Code.variableData x), (-(c : Int), SourceTermGraph.Code.variableData z)]))
      (SourceTermGraph.Code.atom ((c : Int) - 1, [(c, SourceTermGraph.Code.variableData z), (-1, SourceTermGraph.Code.variableData x)]))

def inverse (u z x : Nat) : Nat :=
  SourceTermGraph.Code.conjunction
    (SourceTermGraph.Code.equation (-1, [(1, SourceTermGraph.Code.variableData u), (-1, SourceTermGraph.Code.variableData z)]))
    (SourceTermGraph.Code.conjunction
      (disjunction (SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData z)]))
        (SourceTermGraph.Code.atom (0, [(1, SourceTermGraph.Code.variableData x), (-1, SourceTermGraph.Code.phiData z)])))
      (SourceTermGraph.Code.atom (-1, [(1, SourceTermGraph.Code.phiData u), (-1, SourceTermGraph.Code.variableData x)])))

/-- Literal original postorder graph, jointly in the start and term code.
The same branch offsets and name roles are retained. Both H tags are explicit
falsity; no semantic/H-free test is an input and no graph is assumed effective. -/
def graph (start code : Nat) : Nat :=
  if code % 10 = 0 then SourceTermGraph.Code.equation (SourceTermGraph.Code.numeralRow start (code / 10))
  else if code % 10 = 1 then SourceTermGraph.Code.equation (SourceTermGraph.Code.variableRow start (code / 10))
  else if code % 10 = 2 then
    let a := (code / 10).unpair.1
    let b := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (SourceTermGraph.Code.conjunction (graph (start + nodeCount a) b)
        (SourceTermGraph.Code.equation (SourceTermGraph.Code.additionRow (output start code)
          (output start a) (output (start + nodeCount a) b))))
  else if code % 10 = 3 then
    let a := (code / 10).unpair.1
    let b := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (SourceTermGraph.Code.conjunction (graph (start + nodeCount a) b)
        (subtraction (output start code) (output start a) (output (start + nodeCount a) b)))
  else if code % 10 = 4 then
    let a := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (SourceTermGraph.Code.equation (multiplyRow (output start code) (output start a) (code / 10).unpair.1))
  else if code % 10 = 5 then
    let a := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (graph start a)
      (division (output start code) (output start a) (code / 10).unpair.1)
  else if code % 10 = 6 then
    SourceTermGraph.Code.conjunction (graph start (code / 10))
      (SourceTermGraph.Code.equation (SourceTermGraph.Code.phiRow (output start code) (output start (code / 10))))
  else if code % 10 = 8 then
    SourceTermGraph.Code.conjunction (graph start (code / 10))
      (inverse (start + nodeCount (code / 10)) (output start code) (output start (code / 10)))
  else 1
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 10 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 10)
    have hr := Nat.unpair_right_le (code / 10)
    omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCode
