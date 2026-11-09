module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Runner
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

structure Work where
  row : Row
  guard : Formula

structure State where
  paid : Nat
  work : List Work
  finished : List RowCase

def admitted (D : Nat) (r : Row) : Bool :=
  decide (3 ≤ D) && r.2.all (fun a => FullWordGuardCompletion.admittedWord D a.2.2)

def initial (r : Row) : State := ⟨rowTail r,[⟨r,.top⟩],[]⟩

def branchWork (parent : Work) (b : Branch) : Option Work :=
  match b.action with
  | .finish _ => none
  | .descend r => some ⟨r,.conj parent.guard b.guard⟩

def branchFinished (parent : Work) (b : Branch) : Option RowCase :=
  match b.action with
  | .finish o => some ⟨.conj parent.guard b.guard,[o]⟩
  | .descend _ => none

/-- Process one current original-name row, retaining every finite branch.
No test of a guard's truth or consistency appears in the actual machine. -/
noncomputable def step (D maximum : Nat) (s : State) : State :=
  match s.work with
  | [] => s
  | parent :: rest =>
      let bs := stage D maximum parent.row
      ⟨max s.paid (foldMax (bs.map Branch.tail)),
        bs.filterMap (branchWork parent) ++ rest,
        bs.filterMap (branchFinished parent) ++ s.finished⟩

noncomputable def run (D maximum : Nat) (r : Row) (fuel : Nat) : State :=
  (step D maximum)^[fuel] (initial r)

/-- The invalid branch stops immediately. All admitted inputs are required
to empty their actual finite work stack; termination is a proof obligation. -/
noncomputable def stopped (D maximum : Nat) (r : Row) (fuel : Nat) : Bool :=
  !(admitted D r) || (run D maximum r fuel).work.isEmpty

/-- Concrete least-stopping search with total default notation. The valid
branch is proved to stop before claiming computability or source correctness. -/
noncomputable def leastFuel (D maximum : Nat) (r : Row) : Nat := by
  classical
  exact if h : ∃ fuel : Nat, stopped D maximum r fuel = true then Nat.find h else 0

def finish (s : State) : Package := ⟨s.paid,s.finished⟩
def invalidPackage : Package := ⟨0,[]⟩

noncomputable def solve (D maximum : Nat) (r : Row) : Package :=
  if admitted D r then finish (run D maximum r (leastFuel D maximum r))
  else invalidPackage

abbrev EncodedState := Nat × List (Row × Nat) × List (Nat × List (Nat × Row))

def encodeState (s : State) : EncodedState :=
  (s.paid,s.work.map (fun w => (w.row,Formula.encode w.guard)),
    s.finished.map (fun c =>
      (Formula.encode c.guard,c.outcomes.map (fun o => (o.tag,o.row)))))

def combineCase (left right : RowCase) : RowCase :=
  ⟨.conj left.guard right.guard,left.outcomes++right.outcomes⟩

def combinePackage (left right : Package) : Package :=
  ⟨max left.tail right.tail,
    left.cases.flatMap (fun l => right.cases.map (combineCase l))⟩

def emptyFamily : Package := ⟨0,[⟨.top,[]⟩]⟩

/-- The actual whole finite-family compiler. Its rows keep original names;
case products concatenate literal outcome lists in their original row order. -/
noncomputable def compile (D maximum : Nat) (rows : List Row) : Package :=
  rows.foldr (fun r out => combinePackage (solve D maximum r) out) emptyFamily

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Runner
