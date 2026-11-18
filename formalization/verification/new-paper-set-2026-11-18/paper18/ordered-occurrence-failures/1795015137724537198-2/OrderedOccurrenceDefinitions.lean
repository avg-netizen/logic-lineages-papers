module
public import LogicLineages.StandardControlCurrent.HyperCloseBlockDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrence
open OrdinalComparison LayeredComparison.SnyatkovCompletion
open NormalForm (Formula Row Summand)

def rows : Formula → List Row
  | .truth | .falsity => []
  | .atom a => [a.row]
  | .negative p => rows p
  | .conjunction p q | .disjunction p q => rows p ++ rows q
abbrev Occurrence := Nat × Nat × Int × Summand
def rowIndex (o : Occurrence) := o.1
def itemIndex (o : Occurrence) := o.2.1
def coefficient (o : Occurrence) := o.2.2.1
def summand (o : Occurrence) := o.2.2.2
def roster (p : Formula) : List Occurrence :=
  (rows p).zipIdx.flatMap fun ri => ri.1.2.zipIdx.map fun ai => (ri.2,ai.2,ai.1.1,ai.1.2)
def nonlinear : Summand → Bool
  | .variable _ => false
  | .phi _ _ | .hyperPhi _ _ _ => true
def live (xs : List Nat) (p : Formula) : List Occurrence :=
  (roster p).filter fun o => coefficient o != 0 && nonlinear (summand o) && (summand o).name ∈ xs
def inactive (xs : List Nat) (p : Formula) : List Nat :=
  xs.filter fun i => !(live xs p).any fun o => (summand o).name == i

def all : List Matrix → Matrix
  | [] => .truth
  | p::ps => .conjunction p (all ps)
def strictOrder (xs : List Nat) : Matrix :=
  all (xs.zipIdx.flatMap fun xi => (xs.drop (xi.2+1)).map fun j =>
    .less (.variable j) (.variable xi.1))
def maximal (xs : List Nat) (p : Formula) (o : Occurrence) : Matrix :=
  all ((live xs p).map fun a => atMost (summand a).term (summand o).term)

/-- tag0 finished; tag1 inactive continuation; tag2 genuine tie reduction;
 tag3 ordered-maximum continuation. Witnesses are raw original names/roster indices. -/
structure Outcome where
  tag : Nat
  bound : List Nat
  witness : Nat
  occurrence : Nat
  matrix : Matrix

def ties (xs : List Nat) (p : Formula) : List Outcome :=
  xs.flatMap fun i => (xs.filter fun j => j != i).map fun j =>
    ⟨2,xs.erase i,i,j,p.compile.substitute i (.variable j)⟩
def ordered (xs : List Nat) (p : Formula) : List Outcome :=
  xs.permutations.flatMap fun ys => (live xs p).zipIdx.map fun oi =>
    ⟨3,ys,(summand oi.1).name,oi.2,
      .conjunction (strictOrder ys) (.conjunction (maximal xs p oi.1) p.compile)⟩
def dispatch (xs : List Nat) (p : Formula) : List Outcome :=
  if xs=[] then [⟨0,[],0,0,p.compile⟩]
  else if inactive xs p=[] then ties xs p ++ ordered xs p
  else (inactive xs p).map fun i => ⟨1,xs,i,0,p.compile⟩
def outputCode (o : Outcome) : Nat × List Nat × Nat × Nat × Nat :=
  (o.tag,o.bound,o.witness,o.occurrence,o.matrix.encode)
def holds (o : Outcome) (ν : Nat → Nat) : Prop :=
  HyperCloseBlock.existsNames o.bound o.matrix ν
end LogicLineages.StandardControlCurrent.OrderedOccurrence
