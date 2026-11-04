module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindow

/-- SourceII5 has the opposite orientation to the accepted plus window:
Phi(x_i+e)<=Phi(anchor)<=c*Phi(x_i+e). The original domain stays explicit. -/
def closeMatrix (i : Nat) (anchor : Term) (e : Int) (c : Nat) : Matrix :=
  .conjunction (shiftDomain (.variable i) e)
    (.conjunction (atMost (.phi (shiftTerm (.variable i) e)) (.phi anchor))
      (atMost (.phi anchor) (.multiply c (.phi (shiftTerm (.variable i) e)))))

/-- The actual MINUS displacement. Natural subtraction totalizes the literal
numeric syntax; original guards are retained in every branch. Completeness
must prove anchor>=d and the original signed equality, rather than assume it. -/
def replacementTerm (anchor : Term) (e : Int) (d : Nat) : Term :=
  shiftTerm (.subtract anchor (.numeral d)) (-e)

def finiteCases (i : Nat) (anchor : Term) (e : Int) (c : Nat) (p : Matrix) : Matrix :=
  Matrix.any ((List.range (c + 1)).map (fun d =>
    (Matrix.conjunction (closeMatrix i anchor e c) p).substitute i (replacementTerm anchor e d)))

namespace Code
abbrev Input := WindowCode.Input
def input (i anchor : Nat) (e : Int) (c p : Nat) : Input := (i, anchor, e, c, p)
def replacement (anchor : Nat) (e : Int) (d : Nat) : Nat :=
  WindowCode.shift (WindowCode.subtract anchor (WindowCode.numeral d)) (-e)
def close (i anchor : Nat) (e : Int) (c : Nat) : Nat :=
  WindowCode.conjunction (WindowCode.domain (WindowCode.var i) e)
    (WindowCode.conjunction
      (WindowCode.atMost (WindowCode.phi (WindowCode.shift (WindowCode.var i) e)) (WindowCode.phi anchor))
      (WindowCode.atMost (WindowCode.phi anchor)
        (WindowCode.multiply c (WindowCode.phi (WindowCode.shift (WindowCode.var i) e)))))
def finiteCases (p : Input) : Nat :=
  WindowCode.any ((List.range (p.2.2.2.1 + 1)).map (fun d =>
    WindowCode.matrixSubstitute p.1 (replacement p.2.1 p.2.2.1 d)
      (WindowCode.conjunction (close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2)))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ReverseWindow
