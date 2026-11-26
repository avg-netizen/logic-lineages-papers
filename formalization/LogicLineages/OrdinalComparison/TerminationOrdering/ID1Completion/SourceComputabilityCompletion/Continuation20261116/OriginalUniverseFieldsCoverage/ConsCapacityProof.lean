module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityRuleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryCapacityArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCapacityProof
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
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem atChildren (n : Nat) (raw typ left right leftType rightType lv ls ll rv rs rl maximum : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hs : Nonempty (Derivation body Delta (eqn (xs 9) (add ls rs))))
    (hl : Nonempty (Derivation body Delta (eqn (xs 10) maximum)))
    (hmax : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum ll rl)))
    (hleft : Nonempty (Derivation body Delta (capacity n left
      (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll))))
    (hright : Nonempty (Derivation body Delta (capacity n right
      (ChildFrameProof.frame xs rightType (xs 6) (xs 7) rv rs rl)))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply CapacityRuleProof.introduce n raw xs
  intro beta j Theta hj labels bound hsize hlabel
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hmj := renameInto hm j Theta hj
  have hsj := renameInto hs j Theta hj
  have hlj := renameInto hl j Theta hj
  have hmaxj := renameInto hmax j Theta hj
  have hleftj := renameInto hleft j Theta hj
  have hrightj := renameInto hright j Theta hj
  rw [graph3Rename] at hcj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hgj hmj hmaxj
  simp only [eqnRelabel,sucRelabel,addRelabel] at hsj hlj
  rw [CapacitySyntaxProof.capacityRename] at hleftj hrightj
  have hsz := BinaryCapacityArithmeticProof.sizes true ((xs 9).relabel j) (ls.relabel j) (rs.relabel j) bound hsj hsize
  have hlb := BinaryCapacityArithmeticProof.labels ((xs 10).relabel j) (ll.relabel j) (rl.relabel j)
    (maximum.relabel j) labels hlj hmaxj hlabel
  have hlf := CapacityBindingProof.applyBound n (left.relabel j)
    (fun i => (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll i).relabel j) labels bound
    hleftj (andLeft hsz) (andLeft hlb)
  have hrf := CapacityBindingProof.applyBound n (right.relabel j)
    (fun i => (ChildFrameProof.frame xs rightType (xs 6) (xs 7) rv rs rl i).relabel j) labels bound
    hrightj (andRight hsz) (andRight hlb)
  exact (OriginalEnumerationFields.BinaryProof.internalCons n body beta Theta (raw.relabel j)
    ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound
    (typ.relabel j) (left.relabel j) (right.relabel j) hcj).mpr
    (andIntro hgj (andIntro (andIntro hmj hlf) hrf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCapacityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCapacityProof
