module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ContractDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion

def Term.substitute (input : Term) (i : Nat) (replacement : Term) : Term :=
  match input with
  | .numeral n => .numeral n
  | .variable j => if j = i then replacement else .variable j
  | .add a b => .add (a.substitute i replacement) (b.substitute i replacement)
  | .subtract a b => .subtract (a.substitute i replacement) (b.substitute i replacement)
  | .multiply c a => .multiply c (a.substitute i replacement)
  | .divide c a => .divide c (a.substitute i replacement)
  | .phi a => .phi (a.substitute i replacement)
  | .hyper a => .hyper (a.substitute i replacement)
  | .phiInverse a => .phiInverse (a.substitute i replacement)
  | .hyperInverse a => .hyperInverse (a.substitute i replacement)

def Matrix.substitute (input : Matrix) (i : Nat) (replacement : Term) : Matrix :=
  match input with
  | .truth => .truth
  | .falsity => .falsity
  | .equal a b => .equal (a.substitute i replacement) (b.substitute i replacement)
  | .less a b => .less (a.substitute i replacement) (b.substitute i replacement)
  | .divisible m a => .divisible m (a.substitute i replacement)
  | .negative p => .negative (p.substitute i replacement)
  | .conjunction p q => .conjunction (p.substitute i replacement) (q.substitute i replacement)
  | .disjunction p q => .disjunction (p.substitute i replacement) (q.substitute i replacement)

/-- Literal total signed translation; on its separately retained source domain
it equals the original signed integer argument, without a clamping convention. -/
def shiftTerm (a : Term) (e : Int) : Term :=
  .subtract (.add a (.numeral e.toNat)) (.numeral (-e).toNat)

def shiftDomain (a : Term) (e : Int) : Matrix :=
  .negative (.less a (.numeral (-e).toNat))

def atMost (a b : Term) : Matrix := .negative (.less b a)

/-- Source pp47--50 coefficient-close argument case. The anchor may contain
arbitrarily many OTHER original variables, H, inverses and nested operations;
it is evaluated once under the SAME original valuation. -/
def closeMatrix (i : Nat) (anchor : Term) (e : Int) (c : Nat) : Matrix :=
  .conjunction (shiftDomain (.variable i) e)
    (.conjunction (atMost (.phi anchor) (.phi (shiftTerm (.variable i) e)))
      (atMost (.phi (shiftTerm (.variable i) e)) (.multiply c (.phi anchor))))

def replacementTerm (anchor : Term) (e : Int) (d : Nat) : Term :=
  shiftTerm (.add anchor (.numeral d)) (-e)

def Matrix.any : List Matrix → Matrix
  | [] => .falsity
  | p :: ps => .disjunction p (Matrix.any ps)

/-- Actual finite substitution compiler: precisely c+1 candidates, no search
over original valuations or solutions. The original comparison/domain guards
remain in every substituted branch, covering all defaults and c=0. -/
def finiteWindow (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (c + 1)).map (fun d =>
    (Matrix.conjunction (closeMatrix i anchor e c) p).substitute i (replacementTerm anchor e d)))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion
