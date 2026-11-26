module
public import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeTargets
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeReadProof
import LogicLineages.PermittedControl.ActualInitialSignedCountCleanupProof
import LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReadsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridge
open OrdinalComparison PreparedProjection
open SignedRowSliceValue (valueAt)
open MixedSameRankResidue (WeightedOperand properOperand)
open ActualInitialSignedCountCleanup (cleanup exactOriginalInitialCleanupTest)
open ActualPaidOrderedSyntaxReads (PaidReadCeiling exactPaidOrderedSyntaxReads)
open ActualPaidSignedRouteReplay (SourceHolds)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)

theorem properClauseMember (family : List (List OriginalPrintedTerminalBitClauses.BitRow))
    (clause : List OriginalPrintedTerminalBitClauses.BitRow) :
    clause ∈ properClauses family ↔ clause ∈ family ∧ AdmittedLiteralClause clause := by
  simp only [properClauses,List.mem_filter,decide_eq_true_eq]

private theorem sourceVal (f ρ : Nat → Nat) (s : SyntaxState) (test : OrderTest) (positive : Bool) :
    (∃ v : Int, valueAt f ρ s.constant s.terms v ∧ test.test.atPolarity positive v) ↔
      SourceHolds f ρ s test positive := by
  constructor
  · rintro ⟨v,value,bit⟩
    obtain ⟨original,frames,live,eq⟩ := (exactActualRowReadState f ρ s.constant s.terms v).mp value
    have η : SyntaxState.mk s.constant s.terms = s := by cases s; rfl
    exact ⟨original,frames.trans η,live,eq.symm ▸ bit⟩
  · rintro ⟨original,frames,live,bit⟩
    have η : s = SyntaxState.mk s.constant s.terms := by cases s; rfl
    exact ⟨_,(exactActualRowReadState f ρ s.constant s.terms _).mpr
      ⟨original,frames.trans η,live,rfl⟩,bit⟩

private theorem signedCleanup (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (s : SyntaxState) (test : OrderTest) (positive : Bool)
    (proper : ∀ t ∈ s.terms, properOperand t.2) (paid : PaidReadCeiling ρ s.terms) :
    (∃ v : Int, valueAt f ρ s.constant s.terms v ∧ test.test.atPolarity positive v) ↔
      SourceHolds f ρ (cleanup s) test positive :=
  (sourceVal f ρ s test positive).trans
    (exactOriginalInitialCleanupTest f B selected ρ s
      (exactPaidOrderedSyntaxReads f B selected ρ s proper paid) test positive)

theorem exactLiteralMixedRowBridge : ExactLiteralMixedRowBridge := by
  intro f B selected ρ row shape paid
  rcases row with ⟨⟨test,c,ts⟩,positive⟩
  let s : SyntaxState := ⟨c,ts⟩
  have ready : ∀ t ∈ s.terms, properOperand t.2 := shape.2
  cases test with
  | equalZero =>
    exact (show (True ∧ _) ↔ _ from ⟨And.right,fun h => ⟨True.intro,h⟩⟩).trans
      (signedCleanup f B selected ρ s .equalZero positive ready paid)
  | nonnegative =>
    exact (show (True ∧ _) ↔ _ from ⟨And.right,fun h => ⟨True.intro,h⟩⟩).trans
      (signedCleanup f B selected ρ s .nonnegative positive ready paid)
  | positive =>
    exact (show (True ∧ _) ↔ _ from ⟨And.right,fun h => ⟨True.intro,h⟩⟩).trans
      (signedCleanup f B selected ρ s .positive positive ready paid)
  | congruence m =>
    exact ⟨And.right,fun h => ⟨shape.1,h⟩⟩

theorem exactLiteralMixedClauseBridge : ExactLiteralMixedClauseBridge := by
  intro f B selected ρ rows proper paid
  constructor
  · intro literal compiled used
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp used
    exact (exactLiteralMixedRowBridge f B selected ρ original (proper original member)
      (paid original member)).mp (literal original member)
  · intro compiled original member
    exact (exactLiteralMixedRowBridge f B selected ρ original (proper original member)
      (paid original member)).mpr (compiled (compileRow original) (List.mem_map.mpr ⟨original,member,rfl⟩))

end LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridge
