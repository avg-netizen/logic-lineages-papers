module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPresentationCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalLiteralCarrierProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalLiteralJUnionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPresentationReinstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAccessibilityRulesProof
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalLiteralPresentationCalibrationProof (exact_LiteralWindowCalibration)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)
open ConditionalJUnionTargets (CarrierUnion UnionClosure)

/-- Rebuild the selected literal tuple when **both** multiset programs are
installed together. The scalar and positive checkers and the actual
p/h/a programs are unchanged. The original rules, totality and alignment
are proved again at that exact new source body. -/
theorem exact_ReinstallLiteralMultisetTuple (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i j : Program 1) (r d : Program 3) (v : Inputs)
    (old : TupleAt xs s W i j r d v) :
    TupleAt xs s W i (jRaw i) r (dCore i r permutation) v := by
  obtain ⟨vals,_,_,cal,unique,oldGuards,aCal,hCal,_,shape,_⟩ := old
  let S := literalData i r
  obtain ⟨newVals,meaning⟩ := exact_LiteralWindowCalibration xs s i r vals.1 vals.2.2.1
  have guards : InputGuards i (jRaw i) r (dCore i r permutation) v.applicationGuard := by
    intro c B α Γ f u y g
    exact oldGuards c B α Γ f u y g
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W valid.2.1 S c
  exact ⟨newVals,meaning,
    ⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
      actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,
      actualOriginalAccessibilityIntroduction S⟩,
    cal,unique,guards,aCal,hCal,total,shape,
    fun c => carriers i (jRaw i) r (dCore i r permutation)
      v.applicationGuard (chosenH v W) (chosenA v) c guards (total c)⟩

/-- The same body with the same preserved original source checker meaning
also supports the fixed binary union and its I/J reasoning prerequisites. -/
theorem exact_ReinstalledLiteralTupleAndJ (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i j : Program 1) (r d : Program 3) (v : Inputs)
    (old : TupleAt xs s W i j r d v) :
    TupleAt xs s W i (jRaw i) r (dCore i r permutation) v ∧
      ∀ c, CarrierUnion (literalData i r) c functionalUnion ∧ UnionClosure (literalData i r) c functionalUnion :=
  ⟨exact_ReinstallLiteralMultisetTuple xs s W valid i j r d v old,fun c =>
    ⟨NumberedWindowInternalFunctionalLiteralCarrierProof.exact_FunctionalLiteralCarrierUnion i r c,
      NumberedWindowInternalFunctionalLiteralJUnionProof.exact_FunctionalLiteralJUnion i r c⟩⟩

#print axioms exact_ReinstallLiteralMultisetTuple
#print axioms exact_ReinstalledLiteralTupleAndJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPresentationReinstallProof
