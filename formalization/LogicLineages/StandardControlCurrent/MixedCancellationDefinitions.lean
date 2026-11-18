module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellation
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)
def selected (r : Row) (bs : List Bool) : List (Int × Summand) :=
  (r.2.zip bs).filterMap (fun a => if a.2 then some a.1 else none)
def retained (r : Row) (bs : List Bool) : Row :=
  (r.1,(r.2.zip bs).filterMap (fun a => if a.2 then none else some a.1))
def coefficientSum (r : Row) (bs : List Bool) : Int := ((selected r bs).map Prod.fst).sum
def equalGuard (r : Row) (bs : List Bool) : Matrix :=
  match selected r bs with
  | [] => .truth
  | a::as => OrderedOccurrence.all (as.map fun b => .equal b.2.term a.2.term)
def enabled (r : Row) (bs : List Bool) : Bool :=
  bs.length == r.2.length && coefficientSum r bs == 0 &&
    (selected r bs).any (fun a => a.1 != 0 && OrderedOccurrence.nonlinear a.2)
def replaceRow (a : Atom) (r : Row) : Atom :=
  match a with
  | .nonnegative _ => .nonnegative r
  | .divisible m _ => .divisible m r

/-- One literal hole, arbitrary Boolean polarity and fixed surrounding guards. -/
inductive Context where
  | hole
  | neg (c : Context)
  | conjLeft (c : Context) (p : Matrix)
  | conjRight (p : Matrix) (c : Context)
  | disjLeft (c : Context) (p : Matrix)
  | disjRight (p : Matrix) (c : Context)
def Context.plug : Context → Matrix → Matrix
  | .hole,p => p
  | .neg c,p => .negative (c.plug p)
  | .conjLeft c q,p => .conjunction (c.plug p) q
  | .conjRight q c,p => .conjunction q (c.plug p)
  | .disjLeft c q,p => .disjunction (c.plug p) q
  | .disjRight q c,p => .disjunction q (c.plug p)
def before (c : Context) (a : Atom) (bs : List Bool) : Matrix :=
  .conjunction (equalGuard a.row bs) (c.plug (guardedAtom a).compile)
def rewritten (c : Context) (a : Atom) (bs : List Bool) : Matrix :=
  .conjunction (equalGuard a.row bs) (c.plug
    (.conjunction (domainFormula a.row).compile
      (replaceRow a (retained a.row bs)).compile))
def step (c : Context) (a : Atom) (bs : List Bool) : Bool × Matrix :=
  if enabled a.row bs then (true,rewritten c a bs) else (false,before c a bs)

/-- Counts every actual term constructor, including nonlinear guard terms. -/
def termNodes : Term → Nat
  | .numeral _ | .variable _ => 1
  | .add a b | .subtract a b => 1+termNodes a+termNodes b
  | .multiply _ a | .divide _ a | .phi a | .hyper a | .phiInverse a | .hyperInverse a => 1+termNodes a
def matrixNodes : Matrix → Nat
  | .truth | .falsity => 1
  | .equal a b | .less a b => 1+termNodes a+termNodes b
  | .divisible _ a => 1+termNodes a
  | .negative p => 1+matrixNodes p
  | .conjunction p q | .disjunction p q => 1+matrixNodes p+matrixNodes q
end LogicLineages.StandardControlCurrent.MixedCancellation
