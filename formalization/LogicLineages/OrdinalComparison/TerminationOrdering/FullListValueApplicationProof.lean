module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationProof
open Source Source.SourceSpecialApplication Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains FullListValueApplication

theorem emptyIdentity : FullListValueApplicationTargets.EmptyIdentity := by
  intro Symbol inst arity I τ P a v
  rfl

theorem nonemptyCalibration : FullListValueApplicationTargets.NonemptyCalibration := by
  intro Symbol inst arity I types τ P hne a v
  cases types with
  | nil => exact False.elim (hne rfl)
  | cons σ rest => rfl

theorem typeTransport : FullListValueApplicationTargets.TypeTransport := by
  intro Symbol inst arity I σ types τ P a v h
  rfl

theorem jointMonotone : FullListValueApplicationTargets.JointMonotone := by
  intro Symbol inst arity I types τ P a b v w hab hvw
  cases types with
  | nil => exact hab
  | cons σ rest =>
    exact MarkedSelectTestProof.fullApplicationMonotone a b hab (fullSuffix (σ::rest) τ (by simp)) v w hvw

theorem restriction : FullListValueApplicationTargets.Restriction := by
  intro Symbol inst arity I types τ P Q h a v
  cases types with
  | nil => rfl
  | cons σ rest =>
    exact RecursiveNaturalDomainsProof.applicationNaturality Symbol inst arity I (arrows (σ::rest) τ) P Q h a
      (fullSuffix (σ::rest) τ (by simp)) v

theorem bottom : FullListValueApplicationTargets.Bottom := by
  intro Symbol inst arity I types τ P v
  cases types with
  | nil => rfl
  | cons σ rest =>
    exact ExecutableDomainBottomProof.allTablesBottom Symbol inst arity I (arrows (σ::rest) τ) P
      ⟨P,fun _ hp => hp⟩ (fullSuffix (σ::rest) τ (by simp)) v

end LogicLineages.OrdinalComparison.TerminationOrdering.FullListValueApplicationProof
