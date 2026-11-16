module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityRuleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)


theorem introduce (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) → ∀ (labels bound : OTerm beta),
      Nonempty (Derivation body Theta (InternalLessThan.strictLess ((xs 9).relabel j) (suc bound))) →
      Nonempty (Derivation body Theta (InternalLessThan.strictLess ((xs 10).relabel j) (suc labels))) →
      Nonempty (Derivation body Theta (OriginalEnumerationFields.Targets.accepted n
        (raw.relabel j) ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply CapacityBindingProof.introduce
  let premise : Formula (alpha ⊕ Fin 2) :=
    InternalLessThan.strictLess ((xs 9).relabel Sum.inl) (suc (.var (.inr 1))) ⊓
    InternalLessThan.strictLess ((xs 10).relabel Sum.inl) (suc (.var (.inr 0)))
  have hp : Nonempty (Derivation body (premise :: Delta.map (fun q => q.relabel Sum.inl)) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := h (alpha ⊕ Fin 2) Sum.inl
    (premise :: Delta.map (fun q => q.relabel Sum.inl))
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)) (.var (.inr 0)) (.var (.inr 1))
    (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityRuleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityRuleProof
