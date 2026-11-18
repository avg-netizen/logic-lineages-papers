module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm
abbrev RawOccurrence := Nat × Nat × Int × Code.ItemData
abbrev Descriptor := Nat × List Nat × Nat × Nat × Nat

/-- Literal row traversal, with total malformed atom decoding. It does not
interpret a valuation or discard any syntactic occurrence. -/
def rows (code : Nat) : List Code.RowData :=
  if code % 6 < 2 then []
  else if code % 6 = 2 then
    [((Encodable.decode (code / 6) : Option Code.AtomData).getD (0,0,0,[])).2.2]
  else if code % 6 = 3 then rows (code / 6)
  else rows (code / 6).unpair.1 ++ rows (code / 6).unpair.2
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def roster (code : Nat) : List RawOccurrence :=
  (rows code).zipIdx.flatMap fun ri => ri.1.2.zipIdx.map fun ai =>
    (ri.2,ai.2,ai.1.1,ai.1.2)
def name (o : RawOccurrence) : Nat := o.2.2.2.2.1
def term (o : RawOccurrence) : Nat := Code.itemTerm o.2.2.2
def live (xs : List Nat) (code : Nat) : List RawOccurrence :=
  (roster code).filter fun o => o.2.2.1 != 0 && o.2.2.2.1 != 0 && name o ∈ xs
def inactive (xs : List Nat) (code : Nat) : List Nat :=
  xs.filter fun i => !(live xs code).any fun o => name o == i
def all (ps : List Nat) : Nat := ps.foldr WindowCode.conjunction 0
def strictOrder (xs : List Nat) : Nat :=
  all (xs.zipIdx.flatMap fun xi => (xs.drop (xi.2+1)).map fun j =>
    WindowCode.less (WindowCode.var j) (WindowCode.var xi.1))
def maximal (os : List RawOccurrence) (o : RawOccurrence) : Nat :=
  all (os.map fun a => WindowCode.atMost (term a) (term o))

def dispatch (xs : List Nat) (code : Nat) : List Descriptor :=
  let matrix := Code.formula code
  let os := live xs code
  let absent := inactive xs code
  if xs=[] then [(0,[],0,0,matrix)]
  else if absent=[] then
    (xs.flatMap fun i => (xs.filter fun j => j != i).map fun j =>
      (2,xs.erase i,i,j,WindowCode.matrixSubstitute i (WindowCode.var j) matrix)) ++
    (xs.permutations.flatMap fun ys => os.zipIdx.map fun oi =>
      (3,ys,name oi.1,oi.2,WindowCode.conjunction (strictOrder ys)
        (WindowCode.conjunction (maximal os oi.1) matrix)))
  else absent.map fun i => (1,xs,i,0,matrix)
end LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
