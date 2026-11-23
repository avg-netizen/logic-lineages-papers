module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstalledCarrierProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedListOpenProof (exact_OpenJRaw exact_IntroJRaw)
open NumberedWindowInternalDirectTypedListInstallTargets

theorem exact_InstalledTypedCarrier : ExactInstalledTypedCarrier := by
  intro i r count c α Γ raw goal
  dsimp only
  intro held next
  let S := data i (jRaw i) r (dCore i r count)
  let B := sourceBody S c
  exact exact_OpenJRaw i B α Γ raw goal
    ((exact_DomainRules i (jRaw i) r (dCore i r count) true c B α Γ raw).1 held) next

theorem exact_IntroInstalledTypedCarrier : ExactIntroInstalledTypedCarrier := by
  intro i r count c α Γ raw decoded
  dsimp only
  intro facts
  let S := data i (jRaw i) r (dCore i r count)
  let B := sourceBody S c
  exact (exact_DomainRules i (jRaw i) r (dCore i r count) true c B α Γ raw).2
    (exact_IntroJRaw i B α Γ raw decoded facts)

#print axioms exact_InstalledTypedCarrier
#print axioms exact_IntroInstalledTypedCarrier
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstalledCarrierProof
