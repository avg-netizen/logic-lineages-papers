module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallPresentationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTupleProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRules
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal OTerm)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH chosenA)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentChecks
  (exact_GivenFreshAlignmentAndCarriers exact_ConcreteParsedFreshCarrierTuple)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets
open NumberedWindowInternalAtomicRefinementReinstallPresentationProof (freshPresentation)

/-- This is only equality of carrier formula syntax. The existing
guard rule has arbitrary body, so it is instantiated again inside
the new actual body where required. No derivation changes its body. -/
private theorem retargetGuards (i j : Program 1) (r R d p : Program 3)
    (old : InputGuards i j r d p) : InputGuards i j R d p := by
  intro c body α Γ f u v h
  have same (x : OTerm α) : carrier (data i j r d) false c x =
      carrier (data i j R d) false c x := rfl
  simpa only [same f,same u] using old c body α Γ f u v h

theorem sameTuple : ExactReinstallSameRefinedTuple := by
  intro xs s W valid i j r d v old
  let R := refined i r
  let S := data i j R d
  obtain ⟨ev,_,_,cal,unique,guards,ha,hh,_,shape,_⟩ := old
  obtain ⟨evaluates,interprets,rules⟩ := freshPresentation xs s i j r d ev
  have guard : InputGuards i j R d v.applicationGuard :=
    retargetGuards i j r R d v.applicationGuard guards
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W valid.2.1 S c
  exact ⟨evaluates,interprets,rules,cal,unique,guard,ha,hh,total,shape,
    fun c => exact_GivenFreshAlignmentAndCarriers i j R d v.applicationGuard (chosenH v W)
      (chosenA v) c guard (total c)⟩

theorem concreteTuple : ExactReinstallConcreteRefinedTuple := by
  intro xs s W valid
  obtain ⟨i,j,r,d,v,proof⟩ := exact_ConcreteParsedFreshCarrierTuple xs s W valid
  have original : TupleAt xs s W i j r d v := proof
  exact ⟨i,j,r,d,v,original,sameTuple xs s W valid i j r d v original⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTupleProof
