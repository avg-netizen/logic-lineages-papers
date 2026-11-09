module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplit
open BlockRows

abbrev State := List Nat × Formula

def atoms : Formula → List Atom
  | .truth | .falsity => []
  | .atom a => [a]
  | .negative p => atoms p
  | .conjunction p q | .disjunction p q => atoms p ++ atoms q
def all : List Formula → Formula
  | [] => .truth
  | p :: ps => .conjunction p (all ps)

/-- One concrete syntax-only cutoff dominates every actual row's coefficient
mass cutoff and every positive residue modulus. Free term VALUES are not read. -/
def atomCharge (a : Atom) : Nat :=
  4 * PlainMaximum.mass a.row + match a with
    | .nonnegative _ => 0
    | .divisible m _ => m + 1
def cutoff (p : Formula) : Nat := 1 + ((atoms p).map atomCharge).sum

def renameSummand (i j : Nat) : NormalForm.Summand → NormalForm.Summand
  | .variable k => .variable (if k = i then j else k)
  | .phi k shift => .phi (if k = i then j else k) shift
  | .hyperPhi k e h => .hyperPhi (if k = i then j else k) e h
def renameRow (i j : Nat) (r : Row) : Row :=
  (r.1, r.2.map (fun a => (a.1, renameSummand i j a.2)))
def rename (i j : Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom (.nonnegative r) => .atom (.nonnegative (renameRow i j r))
  | .atom (.divisible m r) => .atom (.divisible m (renameRow i j r))
  | .negative p => .negative (rename i j p)
  | .conjunction p q => .conjunction (rename i j p) (rename i j q)
  | .disjunction p q => .disjunction (rename i j p) (rename i j q)

def lowerGuard (i c : Nat) : Formula :=
  .atom (.nonnegative ((.numeral 0, .numeral c), [(1, .variable i)]))
def strictMaximumGuard (i j : Nat) : Formula :=
  .atom (.nonnegative ((.numeral 0, .numeral 1), [(1, .variable i), (-1, .variable j)]))
def frame (bound : List Nat) (i : Nat) (p : Formula) : Formula :=
  .conjunction (lowerGuard i (cutoff p))
    (all ((bound.filter (fun j => j != i)).map (strictMaximumGuard i)))

def outsideRow (i : Nat) (r : Row) : Formula :=
  if PlainMaximum.headCoefficient i r = 0 then .truth else
    .disjunction
      (.atom (.nonnegative ((.subtract (PlainMaximum.boundary i r) (.numeral 2), .numeral 1),
        [(-1, .variable i)])))
      (.atom (.nonnegative ((.numeral 0, .add (PlainMaximum.boundary i r) (.numeral 3)),
        [(1, .variable i)])))
def outside (i : Nat) (p : Formula) : Formula :=
  all ((atoms p).map (fun a => match a with
    | .nonnegative r => outsideRow i r
    | .divisible _ _ => .truth))

def linearize (i : Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom (.nonnegative r) => PlainMaximum.linearizeNonnegative i r
  | .atom (.divisible m r) => PlainMaximumResidue.lowerAtom m i r
  | .negative p => .negative (linearize i p)
  | .conjunction p q => .conjunction (linearize i p) (linearize i q)
  | .disjunction p q => .disjunction (linearize i p) (linearize i q)

def bandCandidate (i : Nat) (r : Row) (d : Nat) : Term :=
  .add (.subtract (PlainMaximum.boundary i r) (.numeral 2)) (.numeral d)

/-- Each branch supplies an actual witness for a removed original name.
No maximum guard is required on the small or band branches for soundness. -/
def small (bound : List Nat) (p : Formula) : List State :=
  match bound with
  | [] => []
  | i :: _ => (List.range (cutoff p)).map (fun n =>
      (bound.erase i, p.substitute i (.numeral n)))
def ties (bound : List Nat) (p : Formula) : List State :=
  bound.flatMap (fun i => (bound.filter (fun j => j != i)).map (fun j =>
    (bound.erase i, rename i j p)))
def bands (bound : List Nat) (p : Formula) : List State :=
  bound.flatMap (fun i => (atoms p).flatMap (fun a => match a with
    | .nonnegative r =>
        if PlainMaximum.headCoefficient i r = 0 then [] else
          (List.range 5).map (fun d => (bound.erase i, p.substitute i (bandCandidate i r d)))
    | .divisible _ _ => []))
def far (bound : List Nat) (p : Formula) : List State :=
  bound.map (fun i => (bound.erase i, TiedLinear.eliminate i
    (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))))

/-- The complete finite source dispatcher is fixed here. No elimination,
exhaustiveness or decrease theorem is supplied as an argument or state field. -/
def branches (bound : List Nat) (p : Formula) : List State :=
  small bound p ++ ties bound p ++ bands bound p ++ far bound p

def existsPrefix (ν : Nat → Nat) : List Nat → Formula → Prop
  | [], p => p.eval ν
  | i :: rest, p => ∃ n : Nat, existsPrefix (Function.update ν i n) rest p

/-- Keep already finished branches; expand every other actual finite state. -/
def advance (states : List State) : List State :=
  states.flatMap (fun s => if s.1 = [] then [s] else branches s.1 s.2)
def run (fuel : Nat) (states : List State) : List State := advance^[fuel] states
def project (bound : List Nat) (p : Formula) : Matrix :=
  Matrix.any ((run bound.length [(bound, p)]).map (fun s => s.2.compile))

def termHFree : Term → Bool
  | .numeral _ | .variable _ => true
  | .add a b | .subtract a b => termHFree a && termHFree b
  | .multiply _ a | .divide _ a | .phi a | .phiInverse a => termHFree a
  | .hyper _ | .hyperInverse _ => false
def summandHFree : NormalForm.Summand → Bool
  | .variable _ | .phi _ _ => true
  | .hyperPhi _ _ _ => false
def rowHFree (r : Row) : Bool :=
  termHFree r.1.1 && termHFree r.1.2 && r.2.all (fun a => summandHFree a.2)
def formulaHFree : Formula → Bool
  | .truth | .falsity => true
  | .atom a => rowHFree a.row
  | .negative p => formulaHFree p
  | .conjunction p q | .disjunction p q => formulaHFree p && formulaHFree q
def matrixHFree : Matrix → Bool
  | .truth | .falsity => true
  | .equal a b | .less a b => termHFree a && termHFree b
  | .divisible _ a => termHFree a
  | .negative p => matrixHFree p
  | .conjunction p q | .disjunction p q => matrixHFree p && matrixHFree q

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplit
