module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerProgressProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedUnionScratchTargets (CountMembershipForward)
open NumberedWindowInternalCertifiedUnionInnerProgressProof (UnionCarrierSupply)

/-- Supply the exact existing typed union premise on one fresh selected
body, conditional only on the explicit observer's open membership law. -/
def ExactSelectedUnionCarrierSupply : Prop :=
  ∀ (i : Program 1) (r : Program 3) (count : Program 2) (c : Nat),
    let S := data i (jRaw i) r (dCore i r count)
    CountMembershipForward (sourceBody S c) count → UnionCarrierSupply S c count

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionCarrierTargets
