module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalRawListRecursion (listRec recGraph)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow expected oneTerm Zero poolReady poolCode)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowFieldAlgorithm (unpack)

def scanBase : Program 1 := literal 1 1

/-- The input is [actual row, prior tail result, unchanged raw removed tape]. -/
def rowAt (r : Program 3) : Program 3 :=
  .composition (insertedRow r) ![.projection 2,.projection 0]

def scanStep (r : Program 3) : Program 3 :=
  conjunction (rowAt r) (.projection 1)

def scanLoop (r : Program 3) : Program 2 := listRec scanBase (scanStep r)

/-- Run the actual sparse parser first; on success the loop uses the exact
ordered scratch list. The raw removed tape is not re-encoded or replaced. -/
def scanAt (r : Program 3) : Program 2 := .composition (scanLoop r) ![poolCode,.projection 1]

def scan (r : Program 3) : Program 2 := conjunction poolReady (scanAt r)

/-- Inputs are actual original raw inserted tape, then raw removed tape. -/
def ExactNumericScan : Prop :=
  ∀ (r : Program 3) inserted removed,
    evaluate (scan r) (inserted ::ᵥ removed ::ᵥ nil) =
      ((unpack inserted).any (fun rows => rows.all (expected r removed))).toNat

def loopAccept {α : Type} (r : Program 3) (code removed : OrdinaryArithmetic.Term α) : Formula α :=
  recGraph scanBase (scanStep r) oneTerm code ![removed]

def rowAccept {α : Type} (r : Program 3) (row removed : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (insertedRow r) oneTerm ![removed,row]

def ExactOpenScanParser : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (inserted removed decoded : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (unary parser (OrdinaryArithmetic.succTerm decoded) inserted)) →
    Nonempty (Derivation B Γ (programGraph (scan r) oneTerm ![inserted,removed])) →
    Nonempty (Derivation B Γ (loopAccept r decoded removed))

def ExactOpenScanNil : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (loopAccept r Zero removed))

def ExactOpenScanCons : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code row tail removed : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (programGraph consCode code (Fin.cons row (Fin.cons tail Fin.elim0)))) →
    Nonempty (Derivation B Γ (loopAccept r code removed)) →
    Nonempty (Derivation B Γ (rowAccept r row removed ⊓ loopAccept r tail removed))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
