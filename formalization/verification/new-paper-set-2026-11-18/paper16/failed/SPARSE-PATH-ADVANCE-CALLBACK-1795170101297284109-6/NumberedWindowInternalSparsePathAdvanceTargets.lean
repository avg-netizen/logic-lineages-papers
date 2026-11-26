module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvance
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelope (hopTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCertified)
open NumberedWindowInternalSparsePathAdvance

def encodeState : Option Nat → Nat
  | none => 0
  | some n => n+1

def decodeState : Nat → Option Nat
  | 0 => none
  | n+1 => some n

/-- These are the actual source checks at the literal packed lexical
context. An undecodable packed context is rejected, not treated as []. -/
def packedRaw (entries : Entries) (s : Settings) (ctx ty q w r : Nat) : Bool :=
  (unpack ctx).any (fun g => NumberedWindowConcreteCheckers.step entries s g ty q w r)

def packedLeast (s : Settings) (ctx ty q : Nat) : Option Nat :=
  (unpack ctx).bind (fun g => NumberedWindowScalarAlgorithm.least s g ty q)

def packedOriginalAdvance (entries : Entries) (s : Settings) (ctx ty current hop : Nat) : Option Nat :=
  (unpack ctx).bind (fun g =>
    NumberedWindowPositivePathAlgorithm.advance (NumberedWindowConcreteCheckers.step entries s g ty)
      (NumberedWindowScalarAlgorithm.least s g ty) (decodeState current) hop)

def ActualRawCalibration (entries : Entries) (s : Settings) (raw : Program 5) : Prop :=
  ∀ ctx ty q w r, evaluate raw (ctx ::ᵥ ty ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil) =
    if packedRaw entries s ctx ty q w r then 1 else 0

def ActualLeastCalibration (s : Settings) (least : Program 3) : Prop :=
  ∀ ctx ty q, evaluate least (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil) = encodeState (packedLeast s ctx ty q)

def ActualAdvanceCalibration (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3) : Prop :=
  ∀ ctx ty current hop, evaluate (advance raw least) (ctx ::ᵥ ty ::ᵥ current ::ᵥ hop ::ᵥ nil) =
    encodeState (packedOriginalAdvance entries s ctx ty current hop)

/-- The actual numerical functions must have genuine compiled witnesses.
This target does not merely postulate caller-supplied arbitrary oracles. -/
def ConcreteAdvance : Prop :=
  ∀ (entries : Entries) (s : Settings), ∃ (raw : Program 5) (least : Program 3),
    ActualRawCalibration entries s raw ∧ ActualLeastCalibration s least ∧
      ActualAdvanceCalibration entries s raw least

def AdvanceComposition : Prop :=
  ∀ (entries : Entries) (s : Settings) (raw : Program 5) (least : Program 3),
    ActualRawCalibration entries s raw → ActualLeastCalibration s least →
      ActualAdvanceCalibration entries s raw least

def selectedGraph {α : Type} (raw : Program 5) (least : Program 3)
    (out ctx ty current hop : OTerm α) : Formula α :=
  programGraph (advance raw least) out ![ctx,ty,current,hop]

def acceptedGuard {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current hop : OTerm α) : Formula α :=
  programGraph (advanceGood raw least) (suc z) ![ctx,ty,current,hop]

def selectedTarget {α : Type} (target ctx ty current hop : OTerm α) : Formula α :=
  programGraph (atHop hopTarget) target ![ctx,ty,current,hop]

def actualCalls {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty current target q w r : OTerm α) : Formula α :=
  programGraph raw (suc z) ![ctx,ty,q,w,r] ⊓
    (programGraph least (suc current) ![ctx,ty,q] ⊓
      programGraph least (suc target) ![ctx,ty,r])

/-- Independent output inversion pays the actual guard and the actual
target selector, with no assumed well-formedness or success of the input. -/
def OpenAdvanceGate : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (ctx ty current hop target : OTerm α),
    let a := acceptedGuard raw least ctx ty current hop ⊓ selectedTarget target ctx ty current hop
    let b := selectedGraph raw least (suc target) ctx ty current hop
    Nonempty (Derivation body [] ((a.imp b) ⊓ (b.imp a)))

/-- At an actual supplied hop, invert/introduce acceptance with exactly
the original caller coordinates and both **successful** least outputs. -/
def OpenAdvanceCalls : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (ctx ty current hop target q w r : OTerm α),
    let g := acceptedGuard raw least ctx ty (suc current) hop
    let c := actualCalls raw least ctx ty current target q w r
    Nonempty (Derivation body [] ((hopCertified hop target q w r).imp
      ((g.imp c) ⊓ (c.imp g))))

def OpenNoCurrent : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3)
    (α : Type) (ctx ty hop : OTerm α),
    Nonempty (Derivation body [] (selectedGraph raw least z ctx ty z hop))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
