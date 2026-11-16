module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConstructorArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryMeasureProof
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

theorem atValues (cons : Bool) (n : Nat)
    (raw typ left right pair size label depth lv ls ll dl rv rs rl dr maximum boundLabel canonical : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsConstructors.BinaryRootProof.constructor cons) raw typ left right)))
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
    (hlabel : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum boundLabel ll rl)))
    (hcanonical : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical
      (if cons then add ls rs else suc (add ls rs)) boundLabel)))
    (hl : Nonempty (Derivation body Delta (result false ls dl)))
    (hr : Nonempty (Derivation body Delta (result cons rs dr))) :
    Nonempty (Derivation body Delta (result cons size depth)) := by
  have hvalue := OriginalCodeBoundsConstructors.BinaryValueProof.value cons n raw typ left right
    lv ls ll rv rs rl boundLabel canonical hc hg hlb hrb hlp hrp hlabel hcanonical
  have hs := LeafMeasureProof.measuredSize n raw pair size label canonical
    (if cons then add ls rs else suc (add ls rs)) boundLabel hb hp hvalue hcanonical
  have hdepth := OriginalEnumerationDepth.BinaryValueProof.value cons n raw typ left right dl dr maximum hc hg hld hrd hm
  have he := valueUnique (OriginalEnumerationDepth.depth n) depth (suc maximum) ![raw] hd hdepth
  cases cons
  · exact ConstructorArithmeticProof.binary ls rs dl dr maximum size depth hs he hm
      (ArithmeticProof.termToArguments dl ls (andLeft hl))
      (ArithmeticProof.termToArguments dr rs (andLeft hr))
  · exact ConstructorArithmeticProof.cons ls rs dl dr maximum size depth hs he hm hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryMeasureProof
