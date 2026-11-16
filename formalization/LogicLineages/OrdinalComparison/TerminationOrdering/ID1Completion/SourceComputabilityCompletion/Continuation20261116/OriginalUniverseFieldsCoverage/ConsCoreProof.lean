module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCoreProof
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
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ left right)))
    (ho : Nonempty (Derivation body Delta (observations n arity H true raw xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hmax : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum ll rl)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (add ls rs) maximum)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode (xs 5) typ rightType)))
    (hleft : Nonempty (Derivation body Delta (result n false left
      (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll))))
    (hright : Nonempty (Derivation body Delta (result n true right
      (ChildFrameProof.frame xs rightType (xs 6) (xs 7) rv rs rl)))) :
    Nonempty (Derivation body Delta (result n true raw xs)) := by
  have hg := OriginalEnumerationValidity.ChildProof.cons n raw typ left right hc
    (ObservationsProof.intrinsicGuard n false left _ hleft)
    (ObservationsProof.intrinsicGuard n true right _ hright)
  have hmeasure := BinaryMeasureProof.atValues true n raw typ left right (xs 8) (xs 9) (xs 10)
    lv ls ll rv rs rl maximum canonical hc hg
    (ObservationPartsProof.bounds n arity H true raw xs ho)
    (ObservationPartsProof.pairing n arity H true raw xs ho) hlb hlp hrb hrp hmax hk
  have hcap := ConsCapacityProof.atChildren n raw typ left right leftType rightType lv ls ll rv rs rl maximum xs
    hc hg hm (andLeft hmeasure) (andRight hmeasure) hmax
    (ObservationsProof.enclosing n false left _ hleft) (ObservationsProof.enclosing n true right _ hright)
  have htypes := TypesClosureProof.cons (xs 5) typ rightType (xs 3) ls rs ht hm
    (ObservationsProof.argumentTypes n right _ hright) (ObservationsProof.termPositive n left _ hleft)
  exact andIntro (andIntro hg (TypesClosureProof.boundTransport (xs 5) (xs 3) (xs 9) (add ls rs)
    (andLeft hmeasure) htypes)) hcap

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ConsCoreProof
