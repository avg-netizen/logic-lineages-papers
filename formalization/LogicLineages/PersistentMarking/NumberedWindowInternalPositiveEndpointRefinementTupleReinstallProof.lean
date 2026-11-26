module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTuplePresentationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleReinstallProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRules (carrier)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal OTerm)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH chosenA)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalPositiveEndpointRefinementTupleTargets
open NumberedWindowInternalPositiveEndpointRefinementTuplePresentationProof (freshPresentation)

/-- Only the formula containing the common scalar leaf is reduced;
the original guard rule ranges over the currently given body. -/
private theorem guardsAt (i j : Program 1) (r R d p : Program 3)
    (original : InputGuards i j r d p) : InputGuards i j R d p := by
  intro c body α Γ f u y accepted
  have same (q : OTerm α) : carrier (data i j r d) false c q =
      carrier (data i j R d) false c q := rfl
  simpa only [same f,same u] using original c body α Γ f u y accepted

theorem sameTuple : ExactReinstallEndpointRefinedTuple := by
  intro xs s W valid i j r d v original
  let R := withEndpointCarriers i r
  let S := data i j R d
  obtain ⟨ev,_,_,cal,unique,guards,ha,hh,_,shape,_⟩ := original
  obtain ⟨values,meaning,rules⟩ := freshPresentation xs s i j r d ev
  have newGuards : InputGuards i j R d v.applicationGuard :=
    guardsAt i j r R d v.applicationGuard guards
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W valid.2.1 S c
  exact ⟨values,meaning,rules,cal,unique,newGuards,ha,hh,total,shape,
    fun c => exact_GivenFreshAlignmentAndCarriers i j R d v.applicationGuard
      (chosenH v W) (chosenA v) c newGuards (total c)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleReinstallProof
