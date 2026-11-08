module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathChecker
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalListCodec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def triple {α : Type} (a b c : α) : Fin 3 → α :=
  Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0))

/-- These programs read [source, target, suffix summary]. A nonempty summary
is the original cons of its first raw entry and its accepted-suffix value. -/
def summaryHead : Program 3 :=
  .composition headCode (fun _ : Fin 1 => .projection 2)

def summaryVertex : Program 3 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => summaryHead)

def summaryCertificate : Program 3 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => summaryHead)

def summaryTail : Program 3 :=
  .composition tailCode (fun _ : Fin 1 => .projection 2)

def endpointsEqual : Program 3 :=
  .composition InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0))

def edgeAtSummary (edge : Program 3) : Program 3 :=
  .composition edge (triple (.projection 0) summaryVertex summaryCertificate)

def nonemptyFinish (edge : Program 3) : Program 3 :=
  InternalAcceptance.conjunction (edgeAtSummary edge) summaryTail

def emptyFinish (positive : Bool) : Program 3 :=
  if positive then zero else endpointsEqual

/-- A positive run rejects the empty summary; an ordinary run compares its
endpoints there. Both use exact-one edge and suffix acceptance elsewhere. -/
def finish (edge : Program 3) (positive : Bool) : Program 3 :=
  InternalAcceptance.branch (.projection 2) (emptyFinish positive) (nonemptyFinish edge)

/-- The fold step reads [raw entry, tail summary, target]. -/
def entryVertex : Program 3 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)

def tailRun (edge : Program 3) : Program 3 :=
  .composition (finish edge false) (triple entryVertex (.projection 2) (.projection 1))

def summaryStep (edge : Program 3) : Program 3 :=
  .composition consCode (Fin.cons (.projection 0) (Fin.cons (tailRun edge) Fin.elim0))

/-- The actual original list recursor, with target as its unchanged parameter.
It stores zero for nil and one original cons cell for every nonempty suffix. -/
def summary (edge : Program 3) : Program 2 :=
  listRec (zero : Program 1) (summaryStep edge)

def summaryAt (edge : Program 3) : Program 3 :=
  .composition (summary edge) (Fin.cons (.projection 2) (Fin.cons (.projection 1) Fin.elim0))

/-- The concrete original checker AST reads [source, target, raw path code]. -/
def checker (edge : Program 3) (positive : Bool) : Program 3 :=
  .composition (finish edge positive) (triple (.projection 0) (.projection 1) (summaryAt edge))

def edgeGraph {α : Type} (edge : Program 3) (x y certificate : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph edge (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) (triple x y certificate)

def summaryGraph {α : Type} (edge : Program 3) (out code target : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (summary edge) out (Fin.cons code (Fin.cons target Fin.elim0))

def finishGraph {α : Type} (edge : Program 3) (positive : Bool)
    (out x y state : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (finish edge positive) out (triple x y state)

def checkerGraph {α : Type} (edge : Program 3) (positive : Bool)
    (out x y code : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (checker edge positive) out (triple x y code)

def pathGraph {α : Type} (edge : Program 3) (x y code : OrdinaryArithmetic.Term α) : Formula α :=
  checkerGraph edge false (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x y code

def positiveGraph {α : Type} (edge : Program 3) (x y code : OrdinaryArithmetic.Term α) : Formula α :=
  checkerGraph edge true (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x y code

/-- The guard names the literal paired edge entry and original path cons. -/
def consPremises {α : Type} (code raw tail vertex certificate : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph InternalPairing.pairing raw (Fin.cons vertex (Fin.cons certificate Fin.elim0)) ⊓
    programGraph consCode code (Fin.cons raw (Fin.cons tail Fin.elim0))

/-- Standard evaluation calibration to the unchanged original edge checker.
This is used only by the external evaluation targets. -/
def EdgeCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (edge : Program 3) : Prop :=
  ∀ x y certificate : Nat,
    evaluate edge (x ::ᵥ y ::ᵥ certificate ::ᵥ List.Vector.nil) =
      if NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y certificate
      then 1 else 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathChecker
