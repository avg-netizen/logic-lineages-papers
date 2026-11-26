module
public import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighTargets
import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand properOperand)
open ActualSymbolicZeroSuccessor (SyntaxState cleanSyntax)
open ActualInitialSignedCountCleanup (cleanup)
open ActualShortCountCleanup (LongCountOperand shortLength)
open ActualRankedNormalizationSyntax (LowerStrict)
open ActualPaidSignedRouteReplay (LowerSetup dummy commonMinimum replayMinimum)
open ActualPaidMixedMatrixTuples (Ready rowMinimum exactMixedMatrixMinimum)
open ActualGreatestCongruenceRoute (LowerModulusSetup modulusMinimum)
open ActualPaidOrderedSyntaxReads (PaidReadCeiling readCeiling)
open ActualTraceSignCutoff (terminalCutoffCeiling)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalPrintedLiteralRowBridge (properClauses compileRow originalSyntax AdmittedOperandRow properClauseMember)

private theorem memberBound {α : Type} (cost : α → Nat) (xs : List α) (x : α) (h : x ∈ xs) :
    cost x ≤ xs.foldr (fun a b => max (cost a) b) 0 := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with eq | rest
    · subst a
      exact le_max_left _ _
    · exact (ih rest).trans (le_max_right _ _)

private theorem cleanMember (s : SyntaxState) (t : WeightedOperand) (h : t ∈ (cleanup s).terms) :
    t ∈ s.terms ∧ shortLength t.2 = 0 := by
  obtain ⟨member,kept⟩ := List.mem_filter.mp h
  exact ⟨member,decide_eq_true_eq.mp kept⟩

private theorem longFromShape (op : LowerOperand) (proper : properOperand op) (kept : shortLength op = 0) :
    LongCountOperand op := by
  cases op with
  | coordinate rank => trivial
  | ordinary rank field => trivial
  | count rank lam mu =>
    have hp : ProperField (.entry 0 lam mu) := proper
    refine ⟨hp.1,hp.2.1,hp.2.2,?_⟩
    rintro ⟨k,pos,endpoint⟩
    have gap : shortGapLength lam mu = k := (shortGapRecognition lam mu hp k pos).2.2.mpr endpoint
    exact (ne_of_gt pos) (gap.symm.trans kept)

private theorem signedSetup (B r top : Nat) (baseline : Nat → Nat) (s : SyntaxState)
    (strict : LowerStrict baseline top)
    (shape : ∀ t ∈ s.terms, properOperand t.2)
    (scope : ∀ t ∈ s.terms, t.2.rank < r ∧ t.2.rank ≤ top)
    (fund : ∀ t ∈ s.terms, t.2.rank < top → commonMinimum B r (cleanup s) ≤ baseline t.2.rank) :
    LowerSetup B r top baseline (cleanup s) := by
  refine ⟨strict,?_,?_,?_,?_⟩
  · exact fun t h => scope t (cleanMember s t h).1
  · exact fun t h => shape t (cleanMember s t h).1
  · intro t used
    obtain ⟨original,short⟩ := cleanMember s t used
    exact longFromShape t.2 (shape t original) short
  · exact fun t h lt => fund t (cleanMember s t h).1 lt

private theorem compiledMin (B r top : Nat) (baseline : Nat → Nat)
    (row : ActualPaidMixedMatrixTuples.MixedRow) (z : Nat)
    (h : staticNeed B r row ≤ z) (previous : rankedPredecessor top baseline ≤ z) :
    rowMinimum B r top baseline row ≤ z := by
  cases row with
  | signed row =>
    change max (commonMinimum B r row.source)
      (max (terminalCutoffCeiling r (dummy row.source)) (rankedPredecessor top baseline)) ≤ z
    exact max_le ((le_max_left _ _).trans h) (max_le ((le_max_right _ _).trans h) previous)
  | modular m s positive => exact h

private theorem paidCompiled (B r top : Nat) (baseline : Nat → Nat) (row : BitRow)
    (admitted : AdmittedOperandRow row) (strict : LowerStrict baseline top)
    (scope : ∀ t ∈ row.1.2.2, t.2.rank < r ∧ t.2.rank ≤ top)
    (fund : ∀ t ∈ row.1.2.2, t.2.rank < top → staticNeed B r (compileRow row) ≤ baseline t.2.rank) :
    Ready B r top baseline (compileRow row) := by
  rcases row with ⟨⟨test,c,ts⟩,positive⟩
  cases test with
  | equalZero =>
    exact signedSetup B r top baseline ⟨c,ts⟩ strict admitted.2 scope
      (fun t h lt => (le_max_left _ _).trans (fund t h lt))
  | nonnegative =>
    exact signedSetup B r top baseline ⟨c,ts⟩ strict admitted.2 scope
      (fun t h lt => (le_max_left _ _).trans (fund t h lt))
  | positive =>
    exact signedSetup B r top baseline ⟨c,ts⟩ strict admitted.2 scope
      (fun t h lt => (le_max_left _ _).trans (fund t h lt))
  | congruence m =>
    exact ⟨admitted.1,fun t h => ⟨(scope t h).2,admitted.2 t h⟩,fund⟩

theorem exactOriginalLiteralReady : ExactOriginalLiteralReady := by
  intro B r top baseline family setup z high rows member
  obtain ⟨literal,admitted⟩ := (properClauseMember family rows).mp member
  have structural (row : BitRow) (used : row ∈ rows) : rowNeed B r row ≤ familyNeed B r family :=
    (memberBound (rowNeed B r) rows row used).trans (memberBound (clauseNeed B r) _ rows member)
  have upper : familyNeed B r family ≤ z := (le_max_left _ _).trans high
  have previous : rankedPredecessor top baseline ≤ z := (le_max_right _ _).trans high
  refine ⟨?_,?_,?_⟩
  · intro row used t occurs
    have a : readCeiling row.1.2.2 ≤ familyNeed B r family := (le_max_left _ _).trans (structural row used)
    rcases lt_or_eq_of_le (setup.scope rows literal row used t occurs).2 with lower | here
    · rw [Function.update_of_ne (ne_of_lt lower)]
      exact a.trans (setup.lower rows member row used t occurs lower)
    · rw [here,Function.update_self]
      exact a.trans upper
  · intro found used
    obtain ⟨row,atRow,rfl⟩ := List.mem_map.mp used
    exact paidCompiled B r top baseline row (admitted row atRow) setup.strict
      (setup.scope rows literal row atRow)
      (fun t occurs below => (le_max_right _ _).trans ((structural row atRow).trans
        (setup.lower rows member row atRow t occurs below)))
  · apply (exactMixedMatrixMinimum B r top baseline (rows.map compileRow) z).mpr
    intro found used
    obtain ⟨row,atRow,rfl⟩ := List.mem_map.mp used
    exact compiledMin B r top baseline (compileRow row) z
      ((le_max_right _ _).trans ((structural row atRow).trans upper)) previous

end LogicLineages.PermittedControl.OriginalRankedLiteralClauseHigh
