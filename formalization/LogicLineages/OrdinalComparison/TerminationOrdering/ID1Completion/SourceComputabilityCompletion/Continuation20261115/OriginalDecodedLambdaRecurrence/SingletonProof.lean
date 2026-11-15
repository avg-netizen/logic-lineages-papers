module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.GuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open NumericDependencyCross
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowSingleton (left right rights pair out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights right z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair z))) :
    Nonempty (Derivation body Delta (graph2 row out rights left)) := by
  let xs : Fin 3 → OTerm alpha := ![right,z,left]
  have he := binaryValue InternalPairing.pairing (.projection 2) (.projection 0) pair left right xs hp
    (projectionValue 2 xs) (projectionValue 0 xs)
  have hs := binaryValue InternalListCodec.consCode rowEntry (.projection 1) out pair z xs ho he (projectionValue 1 xs)
  have hz := InternalRawListRecursionProof.nilValue (body := body) (Gamma := Delta)
    (InternalAcceptance.constantZero 1) rowStep z (Fin.cons left Fin.elim0)
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons left Fin.elim0))
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) rowStep
    rights right z z out (Fin.cons left Fin.elim0) hr hz hs

theorem crossSingleton (left right lefts rights pair out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode lefts left z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rights right z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair z))) :
    Nonempty (Derivation body Delta (graph2 cross out lefts rights)) := by
  let xs : Fin 3 → OTerm alpha := ![left,z,rights]
  have hrow := rowSingleton left right rights pair out hr hp ho
  have hc := binaryValue row (.projection 2) (.projection 0) out rights left xs hrow
    (projectionValue 2 xs) (projectionValue 0 xs)
  have ha := InternalApplicationValidityStackAppendListProof.consBackward out pair z z z out ho
    (InternalApplicationValidityStackAppendListProof.appendZeroValue z) ho
  have hs := binaryValue InternalApplicationValidityStackAppend.append currentRow (.projection 1)
    out out z xs ha hc (projectionValue 1 xs)
  have hz := InternalRawListRecursionProof.nilValue (body := body) (Gamma := Delta)
    (InternalAcceptance.constantZero 1) crossStep z (Fin.cons rights Fin.elim0)
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons rights Fin.elim0))
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) crossStep
    lefts left z z out (Fin.cons rights Fin.elim0) hl hz hs

theorem rawLambda (source target sigma tau q r qs rs child deps : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode qs q z)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rs r z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps child z))) :
    Nonempty (Derivation body Delta (graph2 rawDependencies deps source target)) := by
  let xs : Fin 2 → OTerm alpha := ![source,target]
  have hqs := ArgumentEntriesChildren.InternalProof.internalUnary body alpha Delta false source sigma q qs hs hq
  have hrs := ArgumentEntriesChildren.InternalProof.internalUnary body alpha Delta false target tau r rs ht hr
  have hl := unaryValue ArgumentEntriesChildren.children (.projection 0) qs source xs hqs (projectionValue 0 xs)
  have hh := unaryValue ArgumentEntriesChildren.children (.projection 1) rs target xs hrs (projectionValue 1 xs)
  exact binaryValue cross (.composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 0))
    (.composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 1)) deps qs rs xs
    (crossSingleton q r qs rs child deps hq hr hp hd) hl hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SingletonProof
