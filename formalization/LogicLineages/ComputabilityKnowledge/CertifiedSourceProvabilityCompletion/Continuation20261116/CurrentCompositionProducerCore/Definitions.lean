module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Canonical actual composition-child values in the original parent subtree.
These are evaluator calls, not supplied result terms or evaluation oracles. -/
def childValues {ctx m n : Nat} (f : Program n) (g : Fin n → Program m) (target : Nat)
 (inputs : List.Vector (Term ctx) m) : List.Vector (Term ctx) n :=
 List.Vector.ofFn (fun i => call (target+argumentTag f g i) inputs)
/-- Original calculation formula, using the fixed I codec in Targets. -/
abbrev calculation := @CurrentRecursionProducerCore.childFormula
abbrev producerCode := @CurrentRecursionProducerCore.childCode
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore
