module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCoreProof
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

open InternalAdditionLawsProof (add)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem atValues (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw rootLabel head typ left types right leftType lv ls ll rv rs rl childLabel maximum canonical : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hh : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm0 : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum childLabel ll rl)))
    (hm1 : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum rootLabel childLabel)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc (add ls rs)) maximum)))
    (hleft : Nonempty (Derivation body Delta (result n true left
      (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll))))
    (hright : Nonempty (Derivation body Delta (result n true right
      (ChildFrameProof.frame xs types (xs 6) (xs 7) rv rs rl)))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hg := OriginalEnumerationValidity.HeadChildProof.numbered n raw rootLabel head typ left types right hc hv
    (ObservationsProof.intrinsicGuard n true left _ hleft) (ObservationsProof.intrinsicGuard n true right _ hright)
  have hmeasure := NumberedMeasureProof.atValues n raw rootLabel head typ left types right (xs 8) (xs 9) (xs 10)
    lv ls ll rv rs rl childLabel maximum canonical hc hg
    (ObservationPartsProof.bounds n arity H false raw xs ho)
    (ObservationPartsProof.pairing n arity H false raw xs ho) hlb hlp hrb hrp hm0 hm1 hk
  have hcap := NumberedCapacityProof.atChildren n raw rootLabel head typ left types right leftType
    lv ls ll rv rs rl childLabel maximum xs hc hg hh hm (andLeft hmeasure) (andRight hmeasure) hm0 hm1
    (ObservationsProof.argumentTypes n right _ hright)
    (ObservationsProof.enclosing n true left _ hleft) (ObservationsProof.enclosing n true right _ hright)
  exact andIntro (andIntro hg (CapacityArithmeticProof.unaryPositive (xs 9) (add ls rs) (andLeft hmeasure))) hcap

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCoreProof
