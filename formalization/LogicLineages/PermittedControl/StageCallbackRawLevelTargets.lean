module
public import LogicLineages.PermittedControl.StageCallbackLevelOrderTargets
public import LogicLineages.PermittedControl.RawPacketAlgebraJoinTargets
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeTargets
public import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesTargets
public import LogicLineages.PermittedControl.ActualRawSignedCleanupTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRawLevel
open OrdinalComparison
open PreparedProjection (PreparedPacketCode)
open RawPacketAlgebra (encodePacket)
open StageCallbackCanonicalRoutes (CanonicalActive guard)
open StageCallbackLevelOrder (Entry level levelRoutes levelOrder)
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualCanonicalOperandGrouping (groupRaw)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualRawComparisonCeiling (LabelCode encodeLabel)
open ActualRawCanonicalNodeMetadata (labelsCode tapeHighestCode)
open ActualRawCanonicalAnswerTapes (candidateTapes)
open ActualRawCanonicalNode (RawOutcome groupedCode)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualRawSignedCleanup (cleanupCode)
open ActualSyntaxChargeBudget (syntaxBudgetCode)
open ActualBitFamilyRawLayout (RawBitRow encodeBitRow)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualPreparedSlotAppend (Packet append)
open ActualSelectedSignedRoutePacket (packet)
open OriginalPrintedTerminalBitClauses (BitRow)

/-- A raw frontier entry: the packet codes of the guards met so far and
the current raw syntax. -/
abbrev EntryCode := List PreparedPacketCode × RawSyntax

def encodeEntry (e : Entry) : EntryCode := (e.1.map encodePacket,encodeSyntax e.2)

/-- The order-test tag as it stands in an encoded row header. -/
def orderCode : OrderTest → Nat
  | .equalZero => 0
  | .nonnegative => 1
  | .positive => 2

/-- The four packet-rendering programs the level iteration is parametric
in. Nothing is assumed about them in the definitions below. -/
structure Rendering where
  append : PreparedPacketCode → PreparedPacketCode → PreparedPacketCode
  guard : Nat → List LabelCode → List Nat → PreparedPacketCode
  linear : Nat → RawSyntax → Nat → Bool → PreparedPacketCode
  modular : Nat → Nat → RawSyntax → Bool → PreparedPacketCode

/-- One literal calibration equation per program, on encoder outputs. -/
structure Rendering.Exact (R : Rendering) : Prop where
  append : ∀ l r : Packet,
    R.append (encodePacket l) (encodePacket r) =
      encodePacket (ActualPreparedSlotAppend.append l r)
  guard : ∀ (top : Nat) (grouped : List WeightedOperand) (a : List Answer),
    R.guard top ((labels grouped).map encodeLabel) (a.map Answer.code) =
      encodePacket (StageCallbackCanonicalRoutes.guard top grouped a)
  linear : ∀ (top : Nat) (s : SyntaxState) (test : OrderTest) (positive : Bool),
    R.linear top (encodeSyntax s) (orderCode test) positive =
      encodePacket (canonicalPacket top s.constant s.terms test.test positive)
  modular : ∀ (top m : Nat) (s : SyntaxState) (positive : Bool),
    R.modular top m (encodeSyntax s) positive =
      encodePacket (ActualGreatestCongruenceRoute.packet top m s positive)

/-- The accepted raw node on one syntax and one tape: coefficient and
optional zero successor. -/
def nodeOut (s : RawSyntax) (tape : List Nat) : RawOutcome :=
  groupedCode (s.1,groupRaw s.2,tape)

def stepOfCode (R : Rendering) (top : Nat) (e : EntryCode) (tape : List Nat) : Option EntryCode :=
  if (nodeOut e.2 tape).1 = 0 then
    (nodeOut e.2 tape).2.map
      (fun s => (e.1 ++ [R.guard top (labelsCode (groupRaw e.2.2)) tape],s))
  else none

/-- Children only at a node the raw activity test accepts at `top`. -/
def childrenCode (R : Rendering) (top : Nat) (e : EntryCode) : List EntryCode :=
  if tapeHighestCode top (groupRaw e.2.2) = true then
    (candidateTapes (groupRaw e.2.2)).filterMap (stepOfCode R top e)
  else []

def signedBitCode (order : Nat) (c : Int) : Bool :=
  if order = 0 then decide (c = 0) else if order = 1 then decide (0 ≤ c) else decide (0 < c)

def signedTipCode (order : Nat) (positive : Bool) (c : Int) : PreparedPacketCode :=
  if (if positive then signedBitCode order c else !(signedBitCode order c)) = true then
    encodePacket ([],.truth)
  else encodePacket ([],.falsity)

def leafOfCode (R : Rendering) (top order : Nat) (positive : Bool) (e : EntryCode)
    (tape : List Nat) : Option PreparedPacketCode :=
  if (nodeOut e.2 tape).1 = 0 then none
  else some ((e.1 ++ [R.guard top (labelsCode (groupRaw e.2.2)) tape]).foldr R.append
    (signedTipCode order positive (nodeOut e.2 tape).1))

/-- The rendered packet codes of the stopped candidates at one entry. -/
def leavesCode (R : Rendering) (top order : Nat) (positive : Bool) (e : EntryCode) :
    List PreparedPacketCode :=
  if tapeHighestCode top (groupRaw e.2.2) = true then
    (candidateTapes (groupRaw e.2.2)).filterMap (leafOfCode R top order positive e)
  else [e.1.foldr R.append (R.linear top e.2 order positive)]

def levelCode (R : Rendering) (top : Nat) (start : RawSyntax) : Nat → List EntryCode
  | 0 => [([],start)]
  | n+1 => (levelCode R top start n).flatMap (childrenCode R top)

def signedCode (R : Rendering) (top order : Nat) (positive : Bool) (fuel : Nat) (s : RawSyntax) :
    List PreparedPacketCode :=
  (List.range (fuel+1)).flatMap
    (fun n => (levelCode R top s n).flatMap (leavesCode R top order positive))

/-- The raw per-row program: header tag 3 is a congruence row; any other
tag is read as an order test on the cleaned syntax at its syntax budget. -/
def rowCode (R : Rendering) (r top : Nat) (row : RawBitRow) : List PreparedPacketCode :=
  if row.1.1.1 = 3 then [R.modular top row.1.1.2 row.1.2 row.2]
  else
    signedCode R top row.1.1.1 row.2 (syntaxBudgetCode r (cleanupCode row.1.2).2)
      (cleanupCode row.1.2)

/-- The raw activity test is the typed one on grouped syntax. -/
def ExactRawActivity : Prop :=
  ∀ (top : Nat) (ts : List WeightedOperand),
    tapeHighestCode top (groupRaw (ts.map encodeWeighted)) = true ↔ CanonicalActive top ts

/-- Literal list equation, level by level. -/
def ExactRawLevelEntries : Prop :=
  ∀ (R : Rendering), R.Exact → ∀ (top : Nat) (s : SyntaxState) (n : Nat),
    levelCode R top (encodeSyntax s) n = (level top s n).map encodeEntry

def ExactRawSignedPackets : Prop :=
  ∀ (R : Rendering), R.Exact →
    ∀ (top : Nat) (test : OrderTest) (positive : Bool) (fuel : Nat) (s : SyntaxState),
      signedCode R top (orderCode test) positive fuel (encodeSyntax s) =
        ((levelRoutes top test positive fuel s).map (packet test positive)).map encodePacket

/-- The raw row program emits, in order, the encoded alternatives of the
level-order supplier, for every literal bit row. -/
def ExactRawRowPackets : Prop :=
  ∀ (R : Rendering), R.Exact → ∀ (r top : Nat) (row : BitRow),
    rowCode R r top (encodeBitRow row) = (levelOrder r top row).map encodePacket

def FullStageCallbackRawLevel : Prop :=
  ExactRawActivity ∧ ExactRawLevelEntries ∧ ExactRawSignedPackets ∧ ExactRawRowPackets

end LogicLineages.PermittedControl.StageCallbackRawLevel
