module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionPreparedProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open ActualFiniteOrderBranches (realized)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalMatrixLinearLowerTable (assignment exactLinearLowerTable)
open PreparedProjection (preparedProjectionActual)

theorem exactAlreadyLinearCircuitProjection : ExactAlreadyLinearCircuitProjection := by
  intro f θ B known gates p plain branch member checked _ linear prior positive priorFixed
  let ρ := realized θ branch
  let ops := table known gates p branch
  let minimum := safeMinimum B θ known gates p branch
  let q := formula known gates p branch minimum positive
  let ν := assignment f ρ ops
  have prep := exactAlreadyLinearPreparedCircuit f θ known gates p plain branch member checked linear minimum positive
  have domains := exactLinearLowerTable f ρ (top branch) (renamed known gates p branch)
  have projected := preparedProjectionActual ops q prep.1 ν
  constructor
  · rintro ⟨pr,live,holds⟩
    obtain ⟨z,h⟩ := projected.mp holds
    obtain ⟨ge,source⟩ := (prep.2 ν (domains.2.2.1 live) z).mp h
    exact ⟨z,ge,(priorFixed z).mpr pr,source⟩
  · rintro ⟨z,ge,pr,source⟩
    obtain ⟨snap,actual⟩ := sourceActual f (replay θ known gates p branch z) known gates p plain positive source
    have full := (transportPart θ known gates p branch member checked z (matrix known gates p)
      (fun _ h => h) f snap).mpr actual
    have live := domains.2.2.2 z snap full
    have h := (prep.2 ν (domains.2.2.1 live) z).mpr ⟨ge,source⟩
    exact ⟨(priorFixed z).mp pr,live,projected.mpr ⟨z,h⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
