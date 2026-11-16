module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConstructorArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (valueUnique)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalAdditionLawsProof (add)
open InternalApplicationStepPeelSupportProof (andLeft)
open Continuation20261115 Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValues (n : Nat)
    (raw rootLabel head typ left types right pair size label depth lv ls ll dl rv rs rl dr maximum childLabel boundLabel canonical : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hld : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) dl left)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hrd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) dr right)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum dl dr)))
    (hlabel : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum childLabel ll rl)))
    (hroot : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum boundLabel rootLabel childLabel)))
    (hcanonical : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical
      (suc (add ls rs)) boundLabel)))
    (hl : Nonempty (Derivation body Delta (result true ls dl)))
    (hr : Nonempty (Derivation body Delta (result true rs dr))) :
    Nonempty (Derivation body Delta (result false size depth)) := by
  have hvalue := OriginalCodeBoundsConstructors.NumberedValueProof.value n raw rootLabel head typ left types right
    lv ls ll rv rs rl childLabel boundLabel canonical hc hg hlb hrb hlp hrp hlabel hroot hcanonical
  have hs := LeafMeasureProof.measuredSize n raw pair size label canonical
    (suc (add ls rs)) boundLabel hb hp hvalue hcanonical
  have hdepth := OriginalEnumerationDepth.BinaryValueProof.numbered n raw rootLabel head typ left types right dl dr maximum hc hg hld hrd hm
  have he := valueUnique (OriginalEnumerationDepth.depth n) depth (suc maximum) ![raw] hd hdepth
  exact ConstructorArithmeticProof.binary ls rs dl dr maximum size depth hs he hm hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.NumberedMeasureProof
