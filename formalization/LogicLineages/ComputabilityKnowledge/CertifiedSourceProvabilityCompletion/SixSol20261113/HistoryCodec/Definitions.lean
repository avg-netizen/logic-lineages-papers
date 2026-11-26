module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.StatementChecks

@[expose] public section
/-! Literal arithmetic Programs for the EXISTING square-shell numeric codec.
No program is selected by an opaque primitive-recursive existence theorem. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowPRChildTags List.Vector

/-- Input [a,b]; recurrence on a computes b+a. -/
def add : Program 2 := .recursion (.projection 0)
  (.composition .succ (fun _ => .projection (1 : Fin 3)))

/-- Input [a,b]; recurrence on a computes b*a. -/
def multiply : Program 2 := .recursion (SixSol20261112.Fuel.zeroProgram 1)
  (.composition add (Fin.cases (.projection (1 : Fin 3))
    (Fin.cases (.projection (2 : Fin 3)) Fin.elim0)))

def predecessor : Program 1 := .recursion .zero (.projection (0 : Fin 2))

/-- Input [a,b]; recurrence on a computes b-a. -/
def difference : Program 2 := .recursion (.projection 0)
  (.composition predecessor (fun _ => .projection (1 : Fin 3)))

/-- Input [test,zeroValue,positiveValue]. -/
def select : Program 3 := .recursion (.projection (0 : Fin 2)) (.projection (3 : Fin 4))

def binary {n : Nat} (p : Program 2) (a b : Program n) : Program n :=
  .composition p (Fin.cases b (Fin.cases a Fin.elim0))

def squareFirst : Program 2 := binary multiply (.projection 0) (.projection 0)
def squareSecond : Program 2 := binary multiply (.projection 1) (.projection 1)
def high : Program 2 := binary add (binary add squareFirst (.projection 0)) (.projection 1)
def low : Program 2 := binary add squareSecond (.projection 0)
def pairArguments : Fin 3 → Program 2 :=
  Fin.cases difference (Fin.cases high (Fin.cases low Fin.elim0))
def pair : Program 2 := .composition select pairArguments
/-- Existing list cons encoding: successor of the existing Nat.pair. -/
def cons : Program 2 := .composition .succ (fun _ => pair)

def differenceTag (tag : Nat) : Nat := tag + argumentTag select pairArguments 0

def pairZeroClause {ctx : Nat} (tag : Nat) (a b : Term ctx) : Formula ctx :=
  .imp (.equal (call (differenceTag tag) (a ::ᵥ b ::ᵥ nil)) .zero)
    (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (.add (.add (.mul a a) a) b))

def pairPositiveClause {ctx : Nat} (tag : Nat) (a b k : Term ctx) : Formula ctx :=
  .imp (.equal (call (differenceTag tag) (a ::ᵥ b ::ᵥ nil)) (.succ k))
    (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (.add (.mul b b) a))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCodec
