module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityRuleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCapacityProof
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

open InternalTagArithmeticSyntaxProof (eqnRelabel)
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem atChild (n : Nat) (raw domain child childType extended childPair childSize childLabel : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) domain)))
    (hs : Nonempty (Derivation body Delta (eqn (xs 9) (suc childSize))))
    (hl : Nonempty (Derivation body Delta (eqn (xs 10) childLabel)))
    (hchild : Nonempty (Derivation body Delta (capacity n child
      (ChildFrameProof.frame xs childType extended (suc (xs 7)) childPair childSize childLabel)))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply CapacityRuleProof.introduce n raw xs
  intro beta j Theta hj labels bound hsize hlabel
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hmj := renameInto hm j Theta hj
  have hsj := renameInto hs j Theta hj
  have hlj := renameInto hl j Theta hj
  have hchildj := renameInto hchild j Theta hj
  rw [graph2Rename] at hcj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hgj hmj
  simp only [eqnRelabel,sucRelabel] at hsj hlj
  rw [CapacitySyntaxProof.capacityRename] at hchildj
  have hf := CapacityBindingProof.applyBound n (child.relabel j)
    (fun i => (ChildFrameProof.frame xs childType extended (suc (xs 7)) childPair childSize childLabel i).relabel j)
    labels bound hchildj
    (CapacityArithmeticProof.unarySize ((xs 9).relabel j) (childSize.relabel j) bound hsj hsize)
    (CapacityArithmeticProof.sameLabel ((xs 10).relabel j) (childLabel.relabel j) labels hlj hlabel)
  change Nonempty (Derivation body Theta (OriginalEnumerationFields.Targets.accepted n
    (child.relabel j) ((suc (xs 7)).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound)) at hf
  rw [sucRelabel] at hf
  exact (OriginalEnumerationFields.LambdaProof.internalLambda n body beta Theta (raw.relabel j)
    ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound
    (domain.relabel j) (child.relabel j) hcj).mpr (andIntro hgj (andIntro hmj hf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCapacityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCapacityProof
