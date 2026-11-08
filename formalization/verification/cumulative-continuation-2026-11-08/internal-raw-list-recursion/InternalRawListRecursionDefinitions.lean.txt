module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalListCodec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Repeated original tail, with inputs [number of drops, raw list code]. -/
def drop : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition tailCode (fun _ : Fin 1 => .projection (1 : Fin 3)))

def lookup : Program 2 := .composition headCode (fun _ : Fin 1 => drop)

def zero {k : Nat} : Program k := .composition .zero Fin.elim0

/-- The table starts with the result for the literal nil code. -/
def tableBase {k : Nat} (base : Program k) : Program k :=
  .composition consCode (Fin.cons base (Fin.cons zero Fin.elim0))

def nextCode {k : Nat} : Program (k + 2) :=
  .composition .succ (fun _ : Fin 1 => .projection 0)

def nextHead {k : Nat} : Program (k + 2) :=
  .composition headCode (fun _ : Fin 1 => nextCode)

def nextTail {k : Nat} : Program (k + 2) :=
  .composition tailCode (fun _ : Fin 1 => nextCode)

/-- At table stage i, index i-tail retrieves the previously computed result.
The original subtract program reads [subtrahend,minuend]. -/
def previousIndex {k : Nat} : Program (k + 2) :=
  .composition InternalEqualityTest.subtract
    (Fin.cons nextTail (Fin.cons (.projection 0) Fin.elim0))

def previousValue {k : Nat} : Program (k + 2) :=
  .composition lookup (Fin.cons previousIndex (Fin.cons (.projection 1) Fin.elim0))

/-- Step inputs are [head, recursively computed tail result, parameters]. -/
def nextValue {k : Nat} (step : Program (k + 2)) : Program (k + 2) :=
  .composition step
    (Fin.cons nextHead (Fin.cons previousValue (fun i => .projection i.succ.succ)))

/-- The table is stored newest first in the unchanged successor/pair codec. -/
def tableStep {k : Nat} (step : Program (k + 2)) : Program (k + 2) :=
  .composition consCode (Fin.cons (nextValue step) (Fin.cons (.projection 1) Fin.elim0))

def table {k : Nat} (base : Program k) (step : Program (k + 2)) : Program (k + 1) :=
  .recursion (tableBase base) (tableStep step)

/-- A concrete original PR AST for recursion on every raw list code. The
table is an implementation detail; the source list encoding is unchanged. -/
def listRec {k : Nat} (base : Program k) (step : Program (k + 2)) : Program (k + 1) :=
  .composition headCode (fun _ : Fin 1 => table base step)

def recGraph {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (out code : OrdinaryArithmetic.Term α) (params : Fin k → OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (listRec base step) out (Fin.cons code params)

/-- The exact original recursive-call and step graphs, with one existential
tail-result witness. -/
def consStep {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (out head tail : OrdinaryArithmetic.Term α) (params : Fin k → OrdinaryArithmetic.Term α) : Formula α :=
  existsOne
    (recGraph base step (.var (.inr (0 : Fin 1))) (tail.relabel Sum.inl)
        (fun i => (params i).relabel Sum.inl) ⊓
      programGraph step (out.relabel Sum.inl)
        (Fin.cons (head.relabel Sum.inl) (Fin.cons (.var (.inr (0 : Fin 1)))
          (fun i => (params i).relabel Sum.inl))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursion
