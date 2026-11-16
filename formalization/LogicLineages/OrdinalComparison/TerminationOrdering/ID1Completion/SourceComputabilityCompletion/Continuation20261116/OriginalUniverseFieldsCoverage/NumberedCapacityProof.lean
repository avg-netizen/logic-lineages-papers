module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.CapacityRuleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryCapacityArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
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

theorem atChildren (n : Nat)
    (raw rootLabel head typ left types right leftType lv ls ll rv rs rl childLabel maximum : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hh : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hs : Nonempty (Derivation body Delta (eqn (xs 9) (suc (add ls rs)))))
    (hl : Nonempty (Derivation body Delta (eqn (xs 10) maximum)))
    (hm0 : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum childLabel ll rl)))
    (hm1 : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum rootLabel childLabel)))
    (ht : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed types (xs 3) rs)))
    (hleft : Nonempty (Derivation body Delta (capacity n left
      (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll))))
    (hright : Nonempty (Derivation body Delta (capacity n right
      (ChildFrameProof.frame xs types (xs 6) (xs 7) rv rs rl)))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := by
  apply CapacityRuleProof.introduce n raw xs
  intro beta j Theta hj labels bound hsize hlabel
  have hcj := renameInto hc j Theta hj
  rw [programRename] at hcj
  have hx : (fun i => (![rootLabel,head,typ,left,types,right] i).relabel j) =
      ![rootLabel.relabel j,head.relabel j,typ.relabel j,left.relabel j,types.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hcj
  have hgj := renameInto hg j Theta hj
  have hhj := renameInto hh j Theta hj
  have hmj := renameInto hm j Theta hj
  have hsj := renameInto hs j Theta hj
  have hlj := renameInto hl j Theta hj
  have hm0j := renameInto hm0 j Theta hj
  have hm1j := renameInto hm1 j Theta hj
  have htj := renameInto ht j Theta hj
  have hleftj := renameInto hleft j Theta hj
  have hrightj := renameInto hright j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hgj hmj hm0j hm1j
  simp only [eqnRelabel,sucRelabel,addRelabel] at hsj hlj
  rw [OriginalEnumerationFields.NumberedProof.headAllowedRename] at hhj
  rw [OriginalEnumerationFields.Types.AllowedSyntaxProof.allowedRename] at htj
  rw [CapacitySyntaxProof.capacityRename] at hleftj hrightj
  have hsz := BinaryCapacityArithmeticProof.sizes false ((xs 9).relabel j) (ls.relabel j) (rs.relabel j) bound hsj hsize
  have hroot := BinaryCapacityArithmeticProof.labels ((xs 10).relabel j) (rootLabel.relabel j) (childLabel.relabel j)
    (maximum.relabel j) labels hlj hm1j hlabel
  have hlb := OriginalEnumerationMembership.MaximumProof.forward (ll.relabel j) (rl.relabel j)
    (childLabel.relabel j) labels hm0j (andRight hroot)
  have hlf := CapacityBindingProof.applyBound n (left.relabel j)
    (fun i => (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll i).relabel j) labels bound
    hleftj (andLeft hsz) (andLeft hlb)
  have hrf := CapacityBindingProof.applyBound n (right.relabel j)
    (fun i => (ChildFrameProof.frame xs types (xs 6) (xs 7) rv rs rl i).relabel j) labels bound
    hrightj (andRight hsz) (andRight hlb)
  have htypes := TypesProof.monotone (types.relabel j) ((xs 3).relabel j) (rs.relabel j) bound htj (andRight hsz)
  exact (OriginalEnumerationFields.NumberedProof.internalNumbered n body beta Theta (raw.relabel j)
    ((xs 7).relabel j) ((xs 3).relabel j) ((xs 4).relabel j) labels bound (rootLabel.relabel j)
    (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) hcj).mpr
    (andIntro hgj (andIntro (andIntro (andIntro (andIntro (andIntro (andLeft hroot) hhj) hmj) hlf) htypes) hrf))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
