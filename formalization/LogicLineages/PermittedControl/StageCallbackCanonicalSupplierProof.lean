module
public import LogicLineages.PermittedControl.StageCallbackCanonicalSupplierTargets
import LogicLineages.PermittedControl.StageCallbackSupplierContractProof
import LogicLineages.PermittedControl.StageCallbackLegacyProof
import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesLayoutProof
import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesSemanticsProof
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketFoldProof
import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteProof
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighReadyProof
import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesProof
import LogicLineages.PermittedControl.ActualRawSignedCleanupProof
import LogicLineages.PermittedControl.ActualRawSignedStaticCeilingProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackCanonicalSupplier
open OrdinalComparison
open StageCallbackSupplier (Supplier SupplierShape SupplierExact stageChildren Emits
  exactSuppliedStageCallback)
open StageCallbackLegacy (singleNeed)
open StageCallbackCanonicalRoutes (routes exactCanonicalRouteShape exactCanonicalRoutesAcrossReplay)
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open SignedRowGuardedTest (Test)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualInitialSignedCountCleanup (cleanup)
open ActualRawSignedCleanup (cleanupCode cleanupCalibration)
open ActualRawSignedStaticCeiling (encodeSyntax signCode staticCode)
open ActualEffectiveTerminalSignBound (inputSignBoundCode)
open ActualRawMixedFamilyCeiling (rowBound)
open ActualBitFamilyRawLayout (encodeBitRow)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape packet exactSelectedRoutePacket)
open ActualBoundedSignedRoutes (Route PacketHolds RouteHolds)
open ActualSyntaxChargeBudget (syntaxBudget)
open ActualRankedNormalizationSyntax (LowerStrict)
open ActualPaidOrderedSyntaxReads (PaidReadCeiling)
open ActualPaidSignedRouteReplay (LowerSetup replayMinimum SourceHolds)
open ActualPaidMixedMatrixTuples (MixedRow Source Ready rowMinimum exactMixedMatrixMinimum)
open ActualGreatestCongruenceRoute (exactGreatestCongruenceShape exactGreatestCongruencePacket)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalPrintedLiteralRowBridge (compileRow properClauses AdmittedOperandRow
  AdmittedLiteralClause properClauseMember exactLiteralMixedRowBridge)
open OriginalRankedLiteralClauseHigh (rankedPredecessor highMinimum OriginalSetup
  exactOriginalLiteralReady)

theorem renderedShape (top fuel : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState)
    (route : Route) (member : route ∈ routes top test positive fuel s) :
    Shape (packet test positive route) := by
  obtain ⟨guards,tip⟩ := exactCanonicalRouteShape top fuel test positive s route member
  exact (exactSelectedRoutePacket (fun _ => 0) (fun _ => 0) top 0 test positive route guards tip).1

theorem renderedHolds (f baseline : Nat → Nat) (top z fuel : Nat) (test : OrderTest)
    (positive : Bool) (s : SyntaxState) (route : Route)
    (member : route ∈ routes top test positive fuel s) :
    PacketHolds f baseline top z (packet test positive route) ↔
      RouteHolds f baseline top z test positive route := by
  obtain ⟨guards,tip⟩ := exactCanonicalRouteShape top fuel test positive s route member
  exact (exactSelectedRoutePacket f baseline top z test positive route guards tip).2.1

theorem signedShape (r top : Nat) (src : SyntaxState) (test : OrderTest) (positive : Bool) :
    ∀ q ∈ alternatives r top (.signed ⟨src,test,positive⟩), Shape q := by
  intro q used
  obtain ⟨route,member,rfl⟩ := List.mem_map.mp used
  exact renderedShape top (syntaxBudget r src.terms) test positive src route member

/-- One signed source syntax: the accepted lower setup and replay minimum
plus the static sign payment give both directions on rendered packets. -/
theorem signedExact (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (r top : Nat) (baseline : Nat → Nat) (src : SyntaxState) (test : OrderTest) (positive : Bool)
    (z : Nat) (setup : LowerSetup B r top baseline src)
    (minimum : replayMinimum B r top baseline src ≤ z)
    (signPaid : inputSignBoundCode r src.constant (src.terms.map encodeWeighted) ≤ z) :
    SourceHolds f (Function.update baseline top z) src test positive ↔
      ∃ q ∈ alternatives r top (.signed ⟨src,test,positive⟩), PacketHolds f baseline top z q := by
  refine (exactCanonicalRoutesAcrossReplay f B selected r top baseline src setup z minimum
    signPaid test positive).trans ?_
  constructor
  · rintro ⟨route,member,passes⟩
    exact ⟨packet test positive route,List.mem_map.mpr ⟨route,member,rfl⟩,
      (renderedHolds f baseline top z (syntaxBudget r src.terms) test positive src route
        member).mpr passes⟩
  · rintro ⟨q,used,passes⟩
    obtain ⟨route,member,rfl⟩ := List.mem_map.mp used
    exact ⟨route,member,(renderedHolds f baseline top z (syntaxBudget r src.terms) test positive
      src route member).mp passes⟩

/-- For every order test the raw row majorant contains the static sign
bound of the cleaned syntax. -/
theorem signedSign (B r : Nat) (c : Int) (ts : List WeightedOperand) (bit : Bool) (test : Test)
    (order : ∀ m : Nat, test ≠ .congruence m) :
    inputSignBoundCode r (cleanup ⟨c,ts⟩).constant ((cleanup ⟨c,ts⟩).terms.map encodeWeighted) ≤
      rowBound B r (encodeBitRow ((test,c,ts),bit)) := by
  have inner : signCode r (cleanupCode (encodeSyntax ⟨c,ts⟩)) ≤
      staticCode B r (cleanupCode (encodeSyntax ⟨c,ts⟩)) := le_max_right _ _
  have outer : staticCode B r (cleanupCode (encodeSyntax ⟨c,ts⟩)) ≤
      rowBound B r (encodeBitRow ((test,c,ts),bit)) := by
    cases test with
    | equalZero => exact le_max_right _ _
    | nonnegative => exact le_max_right _ _
    | positive => exact le_max_right _ _
    | congruence m => exact False.elim (order m rfl)
  have total := inner.trans outer
  rw [cleanupCalibration] at total
  exact total

/-- What the interface's payments give for one admitted row. -/
theorem rowReady (B r top : Nat) (baseline : Nat → Nat) (row : BitRow) (z : Nat)
    (admitted : AdmittedOperandRow row) (strict : LowerStrict baseline top)
    (scope : ∀ t ∈ row.1.2.2, t.2.rank < r ∧ t.2.rank ≤ top)
    (lower : ∀ i < top, rowBound B r (encodeBitRow row) ≤ baseline i)
    (high : max (rowBound B r (encodeBitRow row)) (rankedPredecessor top baseline) ≤ z) :
    PaidReadCeiling (Function.update baseline top z) row.1.2.2 ∧
      Ready B r top baseline (compileRow row) ∧
      rowMinimum B r top baseline (compileRow row) ≤ z := by
  have need := singleNeed B r row
  have setup : OriginalSetup B r top baseline [[row]] := by
    refine ⟨strict,?_,?_⟩
    · intro rows inFamily other inRows t inTerms
      have e1 : rows = [row] := List.mem_singleton.mp inFamily
      rw [e1] at inRows
      have e2 : other = row := List.mem_singleton.mp inRows
      rw [e2] at inTerms
      exact scope t inTerms
    · intro _ _ _ _ t _ below
      exact need.trans (lower t.2.rank below)
  have payment : highMinimum B r top baseline [[row]] ≤ z :=
    max_le (need.trans ((le_max_left _ _).trans high)) ((le_max_right _ _).trans high)
  have clause : AdmittedLiteralClause [row] := by
    intro other inRows
    have e : other = row := List.mem_singleton.mp inRows
    rw [e]
    exact admitted
  have member : [row] ∈ properClauses [[row]] :=
    (properClauseMember [[row]] [row]).mpr ⟨List.mem_singleton.mpr rfl,clause⟩
  have ready := exactOriginalLiteralReady B r top baseline [[row]] setup z payment [row] member
  have here : compileRow row ∈ [row].map compileRow :=
    List.mem_map.mpr ⟨row,List.mem_singleton.mpr rfl,rfl⟩
  exact ⟨ready.1 row (List.mem_singleton.mpr rfl),ready.2.1 (compileRow row) here,
    (exactMixedMatrixMinimum B r top baseline ([row].map compileRow) z).mp ready.2.2
      (compileRow row) here⟩

theorem exactCanonicalSupplierShape : ExactCanonicalSupplierShape := by
  intro r top row q used
  rcases row with ⟨⟨test,c,ts⟩,bit⟩
  cases test with
  | equalZero => exact signedShape r top (cleanup ⟨c,ts⟩) .equalZero bit q used
  | nonnegative => exact signedShape r top (cleanup ⟨c,ts⟩) .nonnegative bit q used
  | positive => exact signedShape r top (cleanup ⟨c,ts⟩) .positive bit q used
  | congruence m =>
      have eq := List.mem_singleton.mp used
      subst q
      exact exactGreatestCongruenceShape top m ⟨c,ts⟩ bit

theorem exactCanonicalSupplierExact : ExactCanonicalSupplierExact := by
  intro f B selected r top baseline row z admitted strict scope lower high
  obtain ⟨paidReads,ready,minimum⟩ :=
    rowReady B r top baseline row z admitted strict scope lower high
  have literal := exactLiteralMixedRowBridge f B selected (Function.update baseline top z) row
    admitted paidReads
  refine literal.trans ?_
  rcases row with ⟨⟨test,c,ts⟩,bit⟩
  have rowPaid : rowBound B r (encodeBitRow ((test,c,ts),bit)) ≤ z :=
    (le_max_left _ _).trans high
  cases test with
  | equalZero =>
      exact signedExact f B selected r top baseline (cleanup ⟨c,ts⟩) .equalZero bit z ready
        minimum ((signedSign B r c ts bit .equalZero (by intro m h; cases h)).trans rowPaid)
  | nonnegative =>
      exact signedExact f B selected r top baseline (cleanup ⟨c,ts⟩) .nonnegative bit z ready
        minimum ((signedSign B r c ts bit .nonnegative (by intro m h; cases h)).trans rowPaid)
  | positive =>
      exact signedExact f B selected r top baseline (cleanup ⟨c,ts⟩) .positive bit z ready
        minimum ((signedSign B r c ts bit .positive (by intro m h; cases h)).trans rowPaid)
  | congruence m =>
      refine (exactGreatestCongruencePacket f B selected baseline top m ⟨c,ts⟩ ready z minimum
        bit).2.symm.trans ?_
      constructor
      · intro passes
        exact ⟨_,List.mem_singleton.mpr rfl,passes⟩
      · rintro ⟨p,h,passes⟩
        have eq := List.mem_singleton.mp h
        subst p
        exact passes

theorem exactCanonicalStageCallback : ExactCanonicalStageCallback := by
  intro f B selected high emits
  exact exactSuppliedStageCallback f B canonical exactCanonicalSupplierShape
    (exactCanonicalSupplierExact f B selected) high emits

end LogicLineages.PermittedControl.StageCallbackCanonicalSupplier
