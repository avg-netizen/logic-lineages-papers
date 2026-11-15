module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.RowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open Continuation20261114 NumericDependencyCross
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowCons (left rights right tail rest pair out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights right tail)))
    (hr : Nonempty (Derivation body Delta (graph2 row rest tail left)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair rest))) :
    Nonempty (Derivation body Delta (graph2 row out rights left)) := by
  let xs : Fin 3 → OTerm alpha := ![right,rest,left]
  have he := binaryValue InternalPairing.pairing (.projection 2) (.projection 0) pair left right xs hp
    (projectionValue 2 xs) (projectionValue 0 xs)
  have hs := binaryValue InternalListCodec.consCode rowEntry (.projection 1) out pair rest xs ho he (projectionValue 1 xs)
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) rowStep
    rights right tail rest out (Fin.cons left Fin.elim0) hc hr hs

theorem crossCons (lefts left tail rights rowCode rest out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts left tail)))
    (hr : Nonempty (Derivation body Delta (graph2 cross rest tail rights)))
    (hrow : Nonempty (Derivation body Delta (graph2 row rowCode rights left)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out rowCode rest))) :
    Nonempty (Derivation body Delta (graph2 cross out lefts rights)) := by
  let xs : Fin 3 → OTerm alpha := ![left,rest,rights]
  have hc := binaryValue row (.projection 2) (.projection 0) rowCode rights left xs hrow
    (projectionValue 2 xs) (projectionValue 0 xs)
  have hs := binaryValue InternalApplicationValidityStackAppend.append currentRow (.projection 1)
    out rowCode rest xs ha hc (projectionValue 1 xs)
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) crossStep
    lefts left tail rest out (Fin.cons rights Fin.elim0) ‹Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts left tail))› hr hs

theorem appendTwo (front head firstTail second suffix joined joinedTail : OTerm alpha)
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode front head firstTail)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode firstTail second z)))
    (j0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode joined head joinedTail)))
    (j1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode joinedTail second suffix))) :
    Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)) :=
  InternalApplicationValidityStackAppendListProof.consBackward front head firstTail suffix joinedTail joined h0
    (InternalApplicationValidityStackAppendListProof.consBackward firstTail second z suffix suffix joinedTail h1
      (InternalApplicationValidityStackAppendListProof.appendZeroValue suffix) j1) j0

theorem rowTwo (left right second rights rightsTail pair firstTailPair tailCode out : OTerm alpha)
    (h0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights right rightsTail)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rightsTail second z)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right)))
    (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing firstTailPair left second)))
    (ho0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair tailCode)))
    (ho1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tailCode firstTailPair z))) :
    Nonempty (Derivation body Delta (graph2 row out rights left)) :=
  rowCons left rights right rightsTail tailCode pair out h0
    (OriginalDecodedLambdaRecurrence.SingletonProof.rowSingleton left second rightsTail firstTailPair tailCode h1 hp1 ho1) hp0 ho0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.RowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.RowsProof
