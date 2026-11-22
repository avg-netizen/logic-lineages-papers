module
public import LogicLineages.PermittedControl.OriginalPrintedNewCutoffLowTargets
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedNewCutoffLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedRankedLiteralHigh (cutoff)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows accepts exactPlainTerminalSuffix)
open OriginalMatrixLowDimension (exactLowFamilyDimension)
open HeterogeneousSignedMatrixSlice (Snapshot actualRows sliceRows exactMatrixSnapshots)
open HeterogeneousSignedMatrixLowStrips (exactBranch exactGuardedLowExistential)

theorem sourceSnapshot (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (plain : PreparedProjection.PlainPreparedFormula p) (positive : Bool) :
    SourceAccepts f θ known gates p positive ↔ Residual f θ known gates p positive (matrix known gates p) := by
  let gs := circuit known gates p
  have hg := exactNormalizedCircuitRows f θ gs
  have cut (xs : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p) (passingList θ gs) xs hg.1
  constructor
  · rintro ⟨graph,pol⟩
    obtain ⟨xs,source,yes⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp pol
    exact ⟨xs,(cut xs).mpr ⟨hg.2.mpr graph,source⟩,yes⟩
  · rintro ⟨xs,whole,yes⟩
    obtain ⟨graph,source⟩ := (cut xs).mp whole
    exact ⟨hg.2.mp graph,(exactPlainTerminalSuffix f θ p plain positive).mpr ⟨xs,source,yes⟩⟩

theorem exactPrintedNewCutoffLowAt : ExactPrintedNewCutoffLowAt := by
  intro f B θ known gates p plain positive prior name used below
  let ms := matrix known gates p
  let bound := cutoff B known gates p positive
  have source := sourceSnapshot f θ known gates p plain positive
  constructor
  · rintro ⟨outside,truth⟩
    obtain ⟨xs,actual,yes⟩ := source.mp truth
    obtain ⟨rs,hit,rest⟩ := (exactMatrixSnapshots f θ name (θ name) ms rfl _).mp actual
    let branch := (θ name,sliceRows f name (θ name) ms)
    have member := (exactBranch f name bound ms branch).mpr ⟨below,rfl⟩
    obtain ⟨erase,drop⟩ := exactLowFamilyDimension f name bound ms used branch member rs hit
    exact ⟨branch,member,rs,rfl,hit,erase,drop,outside,xs,rest,yes⟩
  · rintro ⟨branch,member,rs,digit,hit,_,_,outside,xs,rest,yes⟩
    have literal := ((exactBranch f name bound ms branch).mp member).2
    rw [literal,digit] at hit
    have actual := (exactMatrixSnapshots f θ name (θ name) ms rfl _).mpr ⟨rs,hit,rest⟩
    exact ⟨outside,source.mpr ⟨xs,actual,yes⟩⟩

theorem exactPrintedNewCutoffLowStrips : ExactPrintedNewCutoffLowStrips := by
  intro f B ρ known gates p plain positive prior name ms bound used
  let pass : (Nat → Nat) → Snapshot → Prop := fun θ snap =>
    ∃ vals : Snapshot, snap = passingList θ (circuit known gates p) ++ vals ∧ accepts p positive vals
  have low := exactGuardedLowExistential f ρ prior name bound ms pass true
  constructor
  · rintro ⟨a,below,outside,truth⟩
    let θ := Function.update ρ name a
    obtain ⟨xs,actual,yes⟩ := (sourceSnapshot f θ known gates p plain positive).mp truth
    obtain ⟨branch,rs,member,hit,outer,snap,remaining,hpass⟩ :=
      low.mp ⟨a,below,outside,_,actual,⟨xs,rfl,yes⟩⟩
    obtain ⟨ys,rfl,accept⟩ := hpass
    obtain ⟨erase,drop⟩ := exactLowFamilyDimension f name bound ms used branch member rs hit
    exact ⟨branch,member,rs,hit,erase,drop,outer,ys,remaining,accept⟩
  · rintro ⟨branch,member,rs,hit,_,_,outside,xs,actual,yes⟩
    obtain ⟨a,below,outer,snap,original,hpass⟩ :=
      low.mpr ⟨branch,rs,member,hit,outside,_,actual,⟨xs,rfl,yes⟩⟩
    obtain ⟨ys,rfl,accept⟩ := hpass
    exact ⟨a,below,outer,(sourceSnapshot f (Function.update ρ name a) known gates p plain positive).mpr
      ⟨ys,original,accept⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedNewCutoffLow
