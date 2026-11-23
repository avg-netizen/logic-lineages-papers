module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (branch constantZero conjunction)
open ID1Completion.InternalEqualityTest (predecessor)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt tripleTerm)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowDirectAlgorithm (readEntry)

def liftLeft (p : Program 1) : Program 2 := .composition p ![.projection 0]
def liftRight (p : Program 1) : Program 2 := .composition p ![.projection 1]

def parseRemoved : Program 2 := liftLeft parser
def poolReady : Program 2 := branch parseRemoved (constantZero 2) (literal 2 1)
def poolCode : Program 2 := .composition predecessor ![parseRemoved]
def rowGuard : Program 2 := liftRight (guardAt 4)
def rowField (k : Nat) : Program 2 := liftRight (field k)
def memberAt : Program 2 := .composition scratchMember ![poolCode,rowField 1]
def positiveAt (r : Program 3) : Program 2 := .composition r ![rowField 1,rowField 2,rowField 0]

/-- Literal per-insertion checker using unchanged positive code r.
The inputs are original raw removed-list and original raw tag-4 row. -/
def insertedRow (r : Program 3) : Program 2 :=
  conjunction rowGuard (conjunction poolReady (conjunction memberAt (positiveAt r)))

def expected (r : Program 3) (removed row : Nat) : Bool :=
  match unpack removed, readEntry row with
  | some rs, some (target,dominator,cert) =>
      rs.any (fun a => a == dominator) && decide (evaluate r (dominator ::ᵥ cert ::ᵥ target ::ᵥ nil) = 1)
  | _,_ => false

def ExactNumericInsertedRow : Prop :=
  ∀ (r : Program 3) removed row,
    evaluate (insertedRow r) (removed ::ᵥ row ::ᵥ nil) = (expected r removed row).toNat

abbrev Zero {α : Type} : OrdinaryArithmetic.Term α := OrdinaryArithmetic.zeroTerm
def oneTerm {α : Type} : OrdinaryArithmetic.Term α := OrdinaryArithmetic.succTerm Zero

/-- The original parser success and three original selector reports are
explicit proof premises. The output reports the same decoded removed list,
the same physical raw row and same original positive certificate. -/
def ExactOpenInsertedRow : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed row decoded target dominator cert : OrdinaryArithmetic.Term α),
    Nonempty (Derivation B Γ (unary parser (OrdinaryArithmetic.succTerm decoded) removed)) →
    Nonempty (Derivation B Γ (unary (field 0) target row)) →
    Nonempty (Derivation B Γ (unary (field 1) dominator row)) →
    Nonempty (Derivation B Γ (unary (field 2) cert row)) →
    Nonempty (Derivation B Γ (programGraph (insertedRow r) oneTerm ![removed,row])) →
    Nonempty (Derivation B Γ
      (equal row (tripleTerm 4 target dominator cert) ⊓
        (programGraph scratchMember oneTerm ![decoded,dominator] ⊓
          programGraph r oneTerm ![dominator,cert,target])))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
