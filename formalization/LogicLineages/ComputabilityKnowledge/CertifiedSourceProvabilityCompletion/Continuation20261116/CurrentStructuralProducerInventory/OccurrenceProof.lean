module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.OccurrenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem trans {n : Nat} {q : Program n} {u v : Packed}
 (hu : Occurs u q) (hv : Occurs v u.2) : Occurs v q := by
 induction hu with
 | here q h => subst u; exact hv
 | compositionFunction f g _ ih => exact .compositionFunction f g ih
 | compositionArgument f g i _ ih => exact .compositionArgument f g i ih
 | recursionBase f g _ ih => exact .recursionBase f g ih
 | recursionStep f g _ ih => exact .recursionStep f g ih

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.OccurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.OccurrenceProof
