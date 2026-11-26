module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
/-- Exact original recipe at the genuine second-child offset; all numerical
inputs are unrestricted. No correctness predicate is supplied. -/
def Native : Prop := ∀ n (p : Program 1) (q : Program n) (tag offset value : Nat),
 offset = argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1 →
 evaluate program (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) = number p q tag value
/-- Actual installed fixed Program3 graph. Separate genuine rule13 and rule12
occurrences, all original child-call syntax retained. This is a graph contract,
not a source-acceptance oracle or an installation theorem. -/
def Graph : Prop := ∀ arity (root : Program arity) (K : Tags),
 CurrentCallCongruenceProgram.Installation root K →
 ∀ pairTag rule13Tag : Nat,
 (nodes root)[pairTag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes root)[rule13Tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩ →
 ∀ n (p : Program 1) (q : Program n) (tag offset producerTag : Nat),
 offset = argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1 →
 (nodes root)[producerTag]? = some ⟨3,program⟩ →
 ∀ ctx (value : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory root)
  (.equal (call producerTag (Term.numeral tag ::ᵥ Term.numeral offset ::ᵥ value ::ᵥ nil))
   (CorrectedAugmentationErasure.certificate K rule13Tag p q tag value)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.Targets
