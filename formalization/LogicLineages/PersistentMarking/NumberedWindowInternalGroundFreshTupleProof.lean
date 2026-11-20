module
public import LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTupleProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalGroundFreshMembershipProof (givenFreshMember)
open NumberedWindowInternalAtomicRefinementReinstallChecks (exact_ReinstallConcreteRefinedTuple)
open NumberedWindowInternalGroundFreshTargets

theorem reinstalledGround : ExactReinstalledGroundFresh := by
  intro xs s W i j r d v ready context τ α Γ q u ht ha
  obtain ⟨_,_,_,_,_,_,_,_,_,_,align⟩ := ready
  obtain ⟨same⟩ := align context .ground τ α Γ q u ht ha
  exact givenFreshMember i j r d v context α Γ q u ha
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight same)⟩

theorem concreteGround : ExactConcreteGroundFreshTuple := by
  intro xs s W valid
  obtain ⟨i,j,r,d,v,old,ready⟩ := exact_ReinstallConcreteRefinedTuple xs s W valid
  exact ⟨i,j,r,d,v,old,ready,reinstalledGround xs s W i j r d v ready⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTupleProof
