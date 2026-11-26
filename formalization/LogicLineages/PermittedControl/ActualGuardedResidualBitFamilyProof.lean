module
public import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyTargets
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesProof
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesBitsProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsAvailabilityProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGuardedResidualBitFamily
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds clauses zipBits exactPositivePrefixAndBooleanSuffix exactAcceptedVectors)
open ActualGreatestRouteResidual (Residual LowerMatrix rows)
open OriginalPrintedHighResidual (GuardedAccepts guardedRows)
open OriginalProjectedMatrixSemantics (availabilityRows actualLength)
open OriginalPlainTerminalMatrix (accepts)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

theorem exactZipRows (rs : List Row) (bits : List Bool) (len : bits.length = rs.length) :
    (zipBits rs bits).map Prod.fst = rs := by
  induction rs generalizing bits with
  | nil =>
    cases bits with
    | nil => rfl
    | cons b bs => cases len
  | cons r rs ih =>
    cases bits with
    | nil => cases len
    | cons b bs =>
      change r :: (zipBits rs bs).map Prod.fst = r::rs
      rw [ih bs (Nat.succ.inj len)]

theorem exactClauseAppend (f ρ : Nat → Nat) (a b : List BitRow) :
    ClauseHolds f ρ (a ++ b) ↔ ClauseHolds f ρ a ∧ ClauseHolds f ρ b :=
  ⟨fun h => ⟨fun r used => h r (List.mem_append_left _ used),
    fun r used => h r (List.mem_append_right _ used)⟩,
    fun h r used => (List.mem_append.mp used).elim (h.1 r) (h.2 r)⟩

private theorem exactActualCore (f ρ : Nat → Nat) (out : Residual) :
    (∃ branch ∈ clauses (availabilityRows out.ops) out.atoms out.formula true, ClauseHolds f ρ branch) ↔
      LowerMatrix f ρ out := by
  refine (exactPositivePrefixAndBooleanSuffix f ρ (availabilityRows out.ops) out.atoms out.formula true).symm.trans ?_
  constructor
  · rintro ⟨⟨guards,available,positive⟩,values,tail,checked⟩
    have count : guards.length = out.ops.length := by
      simpa only [availabilityRows,List.length_map] using (actualLength f ρ (availabilityRows out.ops) guards available)
    have both := AffineCollapsePairListLow.actualRowsAppend f ρ (availabilityRows out.ops) out.atoms guards values
      (by simpa only [availabilityRows,List.length_map] using count.symm)
    exact ⟨guards,values,count,positive,both.mpr ⟨available,tail⟩,checked⟩
  · rintro ⟨guards,values,count,positive,actual,checked⟩
    have both := AffineCollapsePairListLow.actualRowsAppend f ρ (availabilityRows out.ops) out.atoms guards values
      (by simpa only [availabilityRows,List.length_map] using count.symm)
    obtain ⟨available,tail⟩ := both.mp actual
    exact ⟨⟨guards,available,positive⟩,values,tail,checked⟩

theorem exactGuardedResidualBitFamily : ExactGuardedResidualBitFamily := by
  intro f ρ C top out
  refine ⟨?_,?_⟩
  · intro clause member
    obtain ⟨core,fromCore,rfl⟩ := List.mem_map.mp member
    obtain ⟨bits,used,rfl⟩ := List.mem_map.mp fromCore
    have size := ((exactAcceptedVectors out.formula true out.atoms.length bits).mp used).1
    simp [guardedRows,rows,List.map_map,Function.comp_def,exactZipRows out.atoms bits size,List.append_assoc]
  · constructor
    · rintro ⟨clause,member,checked⟩
      obtain ⟨core,used,rfl⟩ := List.mem_map.mp member
      obtain ⟨chart,body⟩ := (exactClauseAppend f ρ _ _).mp checked
      exact ⟨chart,(exactActualCore f ρ out).mp ⟨core,used,body⟩⟩
    · rintro ⟨chart,body⟩
      obtain ⟨core,used,correct⟩ := (exactActualCore f ρ out).mpr body
      exact ⟨_,List.mem_map.mpr ⟨core,used,rfl⟩,(exactClauseAppend f ρ _ _).mpr ⟨chart,correct⟩⟩

theorem exactGuardedResidualUnion : ExactGuardedResidualUnion := by
  intro f ρ C top outs
  refine ⟨?_,?_⟩
  · intro clause member
    obtain ⟨out,used,atOut⟩ := List.mem_flatMap.mp member
    exact ⟨out,used,(exactGuardedResidualBitFamily f ρ C top out).1 clause atOut⟩
  · constructor
    · rintro ⟨clause,member,actual⟩
      obtain ⟨out,used,atOut⟩ := List.mem_flatMap.mp member
      exact ⟨out,used,(exactGuardedResidualBitFamily f ρ C top out).2.mp ⟨clause,atOut,actual⟩⟩
    · rintro ⟨out,used,actual⟩
      obtain ⟨clause,member,holds⟩ := (exactGuardedResidualBitFamily f ρ C top out).2.mpr actual
      exact ⟨clause,List.mem_flatMap.mpr ⟨out,used,member⟩,holds⟩

end LogicLineages.PermittedControl.ActualGuardedResidualBitFamily
