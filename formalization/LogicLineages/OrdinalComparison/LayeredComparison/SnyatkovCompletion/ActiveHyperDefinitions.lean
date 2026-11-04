module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearWindowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyper

/-- Effective actual-control version of primaryp43 remark3, needed when a
name to be substituted through a hyper-anchor also has an active H occurrence. -/
def bound (e h k : Int) (a : Nat) : Nat :=
  a + 2 * e.natAbs + h.natAbs + k.natAbs + 1

/-- The SAME original j occurs in hyperActive and plainPhi. i may equal j;
there is no independence convention. All original argument domains remain. -/
def guard (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) : Matrix :=
  .conjunction (LinearWindow.domainMatrix i kind e h)
    (.conjunction (HyperWindow.domainMatrix j k l)
      (.conjunction (shiftDomain (.variable j) q)
        (.conjunction
          (atMost (HyperWindow.valueTerm j k l) (LinearWindow.valueTerm i kind e h))
          (atMost (LinearWindow.valueTerm i kind e h)
            (.multiply a (.phi (shiftTerm (.variable j) q)))))))

def finiteCases (i j : Nat) (kind : Bool) (e h k l q : Int) (a : Nat) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (bound k l q a)).map (fun n =>
    (Matrix.conjunction (guard i j kind e h k l q a) p).substitute j (.numeral n)))

namespace Code
abbrev Input := (Nat × Nat) × (Bool × ((Int × Int) × ((Int × Int) × (Int × (Nat × Nat)))))
def input (i j : Nat) (kind : Bool) (e h k l q : Int) (a p : Nat) : Input :=
  ((i, j), (kind, ((e, h), ((k, l), (q, (a, p))))))
def leftName (p : Input) : Nat := p.1.1
def rightName (p : Input) : Nat := p.1.2
def kind (p : Input) : Bool := p.2.1
def leftIndex (p : Input) : Int := p.2.2.1.1
def leftOuter (p : Input) : Int := p.2.2.1.2
def activeIndex (p : Input) : Int := p.2.2.2.1.1
def activeOuter (p : Input) : Int := p.2.2.2.1.2
def plainShift (p : Input) : Int := p.2.2.2.2.1
def coefficient (p : Input) : Nat := p.2.2.2.2.2.1
def matrix (p : Input) : Nat := p.2.2.2.2.2.2
def bound (p : Input) : Nat :=
  ActiveHyper.bound (activeIndex p) (activeOuter p) (plainShift p) (coefficient p)
def guard (p : Input) : Nat :=
  WindowCode.conjunction
    (LinearWindow.Code.domain (leftName p) (kind p) (leftIndex p) (leftOuter p))
    (WindowCode.conjunction
      (HyperWindowCode.domain (rightName p) (activeIndex p) (activeOuter p))
      (WindowCode.conjunction (WindowCode.domain (WindowCode.var (rightName p)) (plainShift p))
        (WindowCode.conjunction
          (WindowCode.atMost
            (HyperWindowCode.value (rightName p) (activeIndex p) (activeOuter p))
            (LinearWindow.Code.value (leftName p) (kind p) (leftIndex p) (leftOuter p)))
          (WindowCode.atMost
            (LinearWindow.Code.value (leftName p) (kind p) (leftIndex p) (leftOuter p))
            (WindowCode.multiply (coefficient p)
              (WindowCode.phi (WindowCode.shift (WindowCode.var (rightName p)) (plainShift p))))))))
def finiteCases (p : Input) : Nat :=
  WindowCode.any ((List.range (bound p)).map (fun n =>
    WindowCode.matrixSubstitute (rightName p) (WindowCode.numeral n)
      (WindowCode.conjunction (guard p) (matrix p))))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ActiveHyper
