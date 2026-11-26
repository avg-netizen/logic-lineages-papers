module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB
theorem literalOuter (pF : Program 1) (c : Code) (sigma : Sentence) :
 Formula.ex (outerMatrix pF c sigma) = prD pF c sigma := rfl
theorem literalInner (pF : Program 1) (c : Code) (sigma : Sentence) (fuel : Nat) :
 Formula.ex (innerMatrix pF c sigma fuel) =
 GorbowStandardInstances.instantiate (outerMatrix pF c sigma) (Term.numeral fuel) := rfl
theorem nativeComparatorReflexivity : Targets.Native = Targets.Native := rfl
theorem sourceComparatorReflexivity : Targets.OnePublishedIntroductionSource = Targets.OnePublishedIntroductionSource := rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
