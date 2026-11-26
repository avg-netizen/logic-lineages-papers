module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BoundsMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
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

theorem atValues (cons : Bool) (n : Nat)
    (raw typ left right pair size label lv ls ll rv rs rl maximum canonical : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsConstructors.BinaryRootProof.constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum ll rl)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical
      (if cons then add ls rs else suc (add ls rs)) maximum))) :
    Nonempty (Derivation body Delta (eqn size (if cons then add ls rs else suc (add ls rs)) ⊓ eqn label maximum)) := by
  have hv := OriginalCodeBoundsConstructors.BinaryValueProof.value cons n raw typ left right
    lv ls ll rv rs rl maximum canonical hc hg hlb hrb hlp hrp hm hk
  exact andIntro (BoundsMeasureProof.measuredSize n raw pair size label canonical
    (if cons then add ls rs else suc (add ls rs)) maximum hb hp hv hk)
    (BoundsMeasureProof.measuredLabel n raw pair size label canonical
    (if cons then add ls rs else suc (add ls rs)) maximum hb hp hv hk)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
