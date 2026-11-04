module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySignDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision
open SnyatkovUnarySign

/-- Exact source unary sign atom (original signed-Phi+linear expression,
desired integer sign). Invalid desired signs simply have false truth. -/
abbrev Atom := Expression × Int
abbrev Clause := List Atom
/-- Finite DNF of unary source atoms; every atom uses the SAME natural input.
Empty matrix is false; empty clause true. No arbitrary Boolean AST conversion
or multi-variable source semantics is hidden in this representation. -/
abbrev Matrix := List Clause

def atomValue (a : Atom) (n : Nat) : Bool := decide ((value a.1 n).sign = a.2)
def clauseValue (C : Clause) (n : Nat) : Bool := C.all (fun a => atomValue a n)
def matrixValue (M : Matrix) (n : Nat) : Bool := M.any (fun C => clauseValue C n)
def tailAtom (a : Atom) : Bool := decide (tailSign a.1 = a.2)
def tailValue (M : Matrix) : Bool := M.any (fun C => C.all tailAtom)

/-- Maximum of ALL original atom domains, even in cancelled/zero terms or
clauses which happen to be false. This is the actual common signed-shift domain. -/
def matrixDomain (M : Matrix) : Nat :=
  ((M.flatten).map (fun a => domainBound a.1)).foldr max 0

/-- A concrete total bound above the common domain and EVERY actual atom
threshold. It does not depend on a solution, solver or asymptotic oracle. -/
def matrixThreshold (M : Matrix) : Nat :=
  matrixDomain M + 1 + ((M.flatten).map (fun a => threshold a.1)).sum

def existsDecision (M : Matrix) : Bool :=
  (List.range (matrixThreshold M)).any (fun n =>
    decide (matrixDomain M ≤ n) && matrixValue M n) || tailValue M

def forallDecision (M : Matrix) : Bool :=
  (List.range (matrixThreshold M)).all (fun n =>
    (!decide (matrixDomain M ≤ n)) || matrixValue M n) && tailValue M

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision
