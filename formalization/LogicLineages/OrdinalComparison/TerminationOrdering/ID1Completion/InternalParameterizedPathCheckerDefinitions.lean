module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathChecker
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalListCodec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def quadruple {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Fin.elim0)))

/-- Finish inputs are [source,target,suffixSummary,parameter]. A nonempty
summary retains the original first paired entry and its suffix acceptance. -/
def summaryHead : Program 4 :=
  .composition headCode (fun _ : Fin 1 => .projection 2)

def summaryVertex : Program 4 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => summaryHead)

def summaryCertificate : Program 4 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => summaryHead)

def summaryTail : Program 4 :=
  .composition tailCode (fun _ : Fin 1 => .projection 2)

def endpointsEqual : Program 4 :=
  .composition InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0))

/-- The identical runtime parameter is passed to every original edge test.
It is not inserted into a vertex or into the source edge certificate. -/
def edgeAtSummary (edge : Program 4) : Program 4 :=
  .composition edge
    (quadruple (.projection 0) summaryVertex summaryCertificate (.projection 3))

def nonemptyFinish (edge : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (edgeAtSummary edge) summaryTail

def emptyFinish (positive : Bool) : Program 4 :=
  if positive then zero else endpointsEqual

def finish (edge : Program 4) (positive : Bool) : Program 4 :=
  InternalAcceptance.branch (.projection 2) (emptyFinish positive) (nonemptyFinish edge)

/-- Step inputs are [rawEntry,tailSummary,target,parameter]. -/
def entryVertex : Program 4 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)

def tailRun (edge : Program 4) : Program 4 :=
  .composition (finish edge false)
    (quadruple entryVertex (.projection 2) (.projection 1) (.projection 3))

def summaryStep (edge : Program 4) : Program 4 :=
  .composition consCode (Fin.cons (.projection 0) (Fin.cons (tailRun edge) Fin.elim0))

/-- The existing raw-list recursor at k=2 carries [target,parameter]
unchanged. The table implementation and original list encoding are retained. -/
def summary (edge : Program 4) : Program 3 :=
  listRec (zero : Program 2) (summaryStep edge)

def summaryAt (edge : Program 4) : Program 4 :=
  .composition (summary edge)
    (InternalPathChecker.triple (.projection 2) (.projection 1) (.projection 3))

/-- Checker inputs are [source,target,rawPathCode,parameter]. Nil remains
reflexive for the ordinary checker and is rejected by the positive checker. -/
def checker (edge : Program 4) (positive : Bool) : Program 4 :=
  .composition (finish edge positive)
    (quadruple (.projection 0) (.projection 1) (summaryAt edge) (.projection 3))

def edgeGraph {α : Type} (edge : Program 4)
    (x y certificate parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph edge (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    (quadruple x y certificate parameter)

def summaryGraph {α : Type} (edge : Program 4)
    (out code target parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (summary edge) out (InternalPathChecker.triple code target parameter)

def finishGraph {α : Type} (edge : Program 4) (positive : Bool)
    (out x y state parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (finish edge positive) out (quadruple x y state parameter)

def checkerGraph {α : Type} (edge : Program 4) (positive : Bool)
    (out x y code parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (checker edge positive) out (quadruple x y code parameter)

def pathGraph {α : Type} (edge : Program 4)
    (x y code parameter : OrdinaryArithmetic.Term α) : Formula α :=
  checkerGraph edge false (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x y code parameter

def positiveGraph {α : Type} (edge : Program 4)
    (x y code parameter : OrdinaryArithmetic.Term α) : Formula α :=
  checkerGraph edge true (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x y code parameter

/-- Precisely the existing original pair-entry and cons graphs. -/
abbrev consPremises {α : Type}
    (code raw tail vertex certificate : OrdinaryArithmetic.Term α) : Formula α :=
  InternalPathChecker.consPremises code raw tail vertex certificate

/-- External calibration of one actual parameter slice to the original
edge test. This proposition is absent from every internal target. -/
def EdgeCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (edge : Program 4) (parameter : Nat) : Prop :=
  ∀ x y certificate : Nat,
    evaluate edge (x ::ᵥ y ::ᵥ certificate ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y certificate
      then 1 else 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathChecker
