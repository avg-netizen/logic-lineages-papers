module
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeGuards
open CommonHeadLargeRow

/-- Finite guards on the labeled original inputs, not on independent heads. -/
inductive Formula where
  | truth | falsity
  | eq (i j : Nat) | lt (i j : Nat) | bound (c i : Nat)
  | conj (p q : Formula) | disj (p q : Formula) | neg (p : Formula)

def Formula.eval (ν : Nat → Nat) : Formula → Prop
  | .truth => True | .falsity => False
  | .eq i j => ν i=ν j | .lt i j => ν i<ν j | .bound c i => c≤ν i
  | .conj p q => p.eval ν ∧ q.eval ν
  | .disj p q => p.eval ν ∨ q.eval ν
  | .neg p => ¬p.eval ν

def Formula.variables : Formula → List Nat
  | .truth | .falsity => []
  | .eq i j | .lt i j => [i,j] | .bound _ i => [i]
  | .conj p q | .disj p q => p.variables++q.variables
  | .neg p => p.variables

def conjunction (ps : List Formula) := ps.foldr Formula.conj .truth
def disjunction (ps : List Formula) := ps.foldr Formula.disj .falsity

def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

def maskCoefficient (cs : List Int) (mask : List Bool) : Int :=
  (List.zipWith (fun a b => if b then a else 0) cs mask).sum

def maskGuard (m i : Nat) (mask : List Bool) : Formula :=
  conjunction ((List.range m).map (fun j =>
    if mask.getD j false then .eq i j else .neg (.eq i j)))

def blockFormula (cs : List Int) (i : Nat) (desired : Int) : Formula :=
  disjunction (((masks cs.length).filter (fun mask => Int.sign (maskCoefficient cs mask)=desired)).map
    (maskGuard cs.length i))

def inputRow (cs : List Int) (ν : Nat → Nat) : Row :=
  cs.zipIdx.map (fun a => (a.1,ν a.2))

def originalThreshold (K : Int) (cs : List Int) : Nat :=
  threshold K (cs.map (fun a => (a,0)))

def canceledFormula (cs : List Int) : Formula :=
  conjunction ((List.range cs.length).map (fun i => blockFormula cs i 0))

def maximalFormula (cs : List Int) (i : Nat) : Formula :=
  conjunction ((List.range cs.length).map (fun j =>
    .disj (.neg (.lt i j)) (blockFormula cs j 0)))

def signFormula (K : Int) (cs : List Int) (desired : Int) : Formula :=
  .disj
    (.conj (if Int.sign K=desired then .truth else .falsity) (canceledFormula cs))
    (if desired=0 then .falsity else disjunction ((List.range cs.length).map (fun i =>
      .conj (blockFormula cs i desired) (maximalFormula cs i))))

def largeFormula (K : Int) (cs : List Int) (desired : Int) : Formula :=
  .conj (conjunction ((List.range cs.length).map (Formula.bound (originalThreshold K cs))))
    (signFormula K cs desired)
end LogicLineages.OrdinalComparison.CommonHeadLargeGuards
