module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLowTargets
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalMatrixActualHighPacket (originalFamilyCeiling)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows accepts exactPlainTerminalSuffix)
open HeterogeneousSignedMatrixSlice (Snapshot actualRows sliceRows exactMatrixSnapshots)
open HeterogeneousSignedMatrixLowStrips (exactBranch exactGuardedLowExistential)

private theorem sourceSnapshot (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (plain : PreparedProjection.PlainPreparedFormula p) (positive : Bool) :
    SourceAccepts f θ known gates p positive ↔
      ∃ vals : Snapshot,
        actualRows f θ (matrix known gates p) (passingList θ (circuit known gates p) ++ vals) ∧
        accepts p positive vals := by
  let gs := circuit known gates p
  have hg := exactNormalizedCircuitRows f θ gs
  have split (xs : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p) (passingList θ gs) xs hg.1
  constructor
  · rintro ⟨graph,pol⟩
    obtain ⟨xs,source,yes⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp pol
    exact ⟨xs,(split xs).mpr ⟨hg.2.mpr graph,source⟩,yes⟩
  · rintro ⟨xs,whole,yes⟩
    obtain ⟨graph,source⟩ := (split xs).mp whole
    exact ⟨hg.2.mp graph,(exactPlainTerminalSuffix f θ p plain positive).mpr ⟨xs,source,yes⟩⟩

theorem exactOriginalSupportLowAt : ExactOriginalSupportLowAt := by
  intro f B θ known gates p plain prior positive rank _ below
  let ms := matrix known gates p
  have source := sourceSnapshot f θ known gates p plain positive
  constructor
  · rintro ⟨pr,sourceAt⟩
    obtain ⟨xs,actual,yes⟩ := source.mp sourceAt
    obtain ⟨residual,live,remaining⟩ :=
      (exactMatrixSnapshots f θ rank (θ rank) ms rfl _).mp actual
    refine ⟨(θ rank,sliceRows f rank (θ rank) ms),residual,?_,rfl,live,pr,xs,remaining,yes⟩
    exact (exactBranch f rank (originalFamilyCeiling B known gates p) ms _).mpr ⟨below,rfl⟩
  · rintro ⟨branch,residual,member,atDigit,hit,pr,xs,remaining,yes⟩
    have shape := ((exactBranch f rank (originalFamilyCeiling B known gates p) ms branch).mp member).2
    rw [shape,atDigit] at hit
    have actual := (exactMatrixSnapshots f θ rank (θ rank) ms rfl _).mpr ⟨residual,hit,remaining⟩
    exact ⟨pr,source.mpr ⟨xs,actual,yes⟩⟩

theorem exactOriginalSupportLowStrips : ExactOriginalSupportLowStrips := by
  intro f B ρ known gates p plain prior positive rank _
  let pass : (Nat → Nat) → Snapshot → Prop := fun θ snap =>
    ∃ vals : Snapshot, snap = passingList θ (circuit known gates p) ++ vals ∧ accepts p positive vals
  have low := exactGuardedLowExistential f ρ prior rank (originalFamilyCeiling B known gates p)
    (matrix known gates p) pass true
  constructor
  · rintro ⟨a,within,pr,source⟩
    let θ := Function.update ρ rank a
    obtain ⟨xs,actual,yes⟩ := (sourceSnapshot f θ known gates p plain positive).mp source
    obtain ⟨branch,residual,member,hit,pr',snap,actual',hpass⟩ :=
      low.mp ⟨a,within,pr,_,actual,⟨xs,rfl,yes⟩⟩
    obtain ⟨ys,rfl,accepted⟩ := hpass
    exact ⟨branch,residual,member,hit,pr',ys,actual',accepted⟩
  · rintro ⟨branch,residual,member,hit,pr,xs,actual,yes⟩
    obtain ⟨a,within,pr',snap,original,hpass⟩ :=
      low.mpr ⟨branch,residual,member,hit,pr,_,actual,⟨xs,rfl,yes⟩⟩
    obtain ⟨ys,rfl,accepted⟩ := hpass
    let θ := Function.update ρ rank a
    exact ⟨a,within,pr',(sourceSnapshot f θ known gates p plain positive).mpr ⟨ys,original,accepted⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLow
