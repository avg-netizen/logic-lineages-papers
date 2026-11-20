module

public import LogicLineages.PersistentMarking.NumberedWindowAddressCheckersProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramProof
import LogicLineages.PersistentMarking.NumberedWindowDirectProgramChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressCheckersProgramProof
open NumberedWindowAddressCheckers NumberedWindowAddressCheckersProgramTargets
open NumberedWindowScalarAlgorithm NumberedWindowScalarProgramProof
open NumberedWindowPositivePathProgramProof (addressPrim)
open NumberedWindowDirectProgramChecks

private theorem indicator (b : Bool) : (if b then 1 else 0) = b.toNat := by cases b <;> rfl

theorem domains : BothDomains := by
  intro s
  obtain ⟨p,h⟩ := NumberedWindowScalarProgramChecks.exact_FixedScalarProgram s
  exact ⟨⟨p,fun n => (h n).trans (indicator _)⟩,exact_MultisetDomainProgram _ (scalarPrim s)⟩

theorem certificates : BothCertificates := by
  intro s step hs
  have hl := leastPrim s
  obtain ⟨p,h⟩ := (NumberedWindowPositivePathProgramProof.programs step (least s) hs hl).2
  have hp := addressPrim hs hl
  exact ⟨⟨p,fun a c b => (h a c b).trans (indicator _)⟩,
    exact_DirectCertificateProgram _ _ (scalarPrim s) hp⟩
end LogicLineages.PersistentMarking.NumberedWindowAddressCheckersProgramProof
