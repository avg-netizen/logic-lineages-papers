module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixTapesTargets
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixTapes
open HeterogeneousSignedMatrixSlice (Snapshot)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows exactPlainTerminalSuffix)
open OriginalMatrixActualReadTape (exactGuardedMatrixTapes)

theorem exactPrintedPlainMatrixTapes : ExactPrintedPlainMatrixTapes := by
  intro f θ known gates p plain positive
  let gs := circuit known gates p
  have core := exactNormalizedCircuitRows f θ gs
  have split (vs : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p)
      (passingList θ gs) vs core.1
  constructor
  · rintro ⟨graph,polarity⟩
    obtain ⟨vs,read,accepted⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp polarity
    have original := (split vs).mpr ⟨core.2.mpr graph,read⟩
    obtain ⟨states,tapes⟩ := (exactGuardedMatrixTapes f θ (matrix known gates p) _).mp original
    exact ⟨vs,states,tapes,accepted⟩
  · rintro ⟨vs,states,tapes,accepted⟩
    have original := (exactGuardedMatrixTapes f θ (matrix known gates p) _).mpr ⟨states,tapes⟩
    obtain ⟨graph,read⟩ := (split vs).mp original
    exact ⟨core.2.mp graph,(exactPlainTerminalSuffix f θ p plain positive).mpr ⟨vs,read,accepted⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixTapes
