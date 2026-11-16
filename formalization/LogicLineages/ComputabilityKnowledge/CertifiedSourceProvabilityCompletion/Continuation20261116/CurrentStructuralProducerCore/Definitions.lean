module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore
open GorbowSyntax
/-- Exact original calculation/code terms, not surrogate success predicates. -/
abbrev calculation {ctx n : Nat}
 (J : LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Tags)
 (target : Nat) (inputs : List.Vector (Term ctx) n) : Term ctx :=
 CurrentRecursionProducerCore.childFormula J target inputs
abbrev code {ctx n : Nat} (producerTag target : Nat) (inputs : List.Vector (Term ctx) n) : Term ctx :=
 CurrentRecursionProducerCore.childCode producerTag target inputs
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore
