module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCoreProof
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
    (raw typ left right leftType rightType lv ls ll rv rs rl maximum canonical : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw typ left right)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hmax : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum ll rl)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc (add ls rs)) maximum)))
    (hleft : Nonempty (Derivation body Delta (result n false left
      (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll))))
    (hright : Nonempty (Derivation body Delta (result n false right
      (ChildFrameProof.frame xs rightType (xs 6) (xs 7) rv rs rl)))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hg := OriginalEnumerationValidity.ChildProof.application n raw typ left right hc
    (ObservationsProof.intrinsicGuard n false left _ hleft)
    (ObservationsProof.intrinsicGuard n false right _ hright)
  have hmeasure := BinaryMeasureProof.atValues false n raw typ left right (xs 8) (xs 9) (xs 10)
    lv ls ll rv rs rl maximum canonical hc hg
    (ObservationPartsProof.bounds n arity H false raw xs ho)
    (ObservationPartsProof.pairing n arity H false raw xs ho) hlb hlp hrb hrp hmax hk
  have hcap := ApplicationCapacityProof.atChildren n raw typ left right leftType rightType lv ls ll rv rs rl maximum xs
    hc hg hm (andLeft hmeasure) (andRight hmeasure) hmax
    (ObservationsProof.enclosing n false left _ hleft) (ObservationsProof.enclosing n false right _ hright)
  exact andIntro (andIntro hg (CapacityArithmeticProof.unaryPositive (xs 9) (add ls rs) (andLeft hmeasure))) hcap

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCoreProof
