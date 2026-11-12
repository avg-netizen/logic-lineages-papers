module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawLambdaAtPairs (raw domain childRaw inner : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner domain childRaw)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) inner))) :
    Nonempty (Derivation body Delta
      (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain childRaw)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons domain (Fin.cons childRaw Fin.elim0)
  have hinner := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    inner domain childRaw xs hi (projectionValue 0 xs) (projectionValue 1 xs)
  exact binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 1)
    (pairOf (.projection 0) (.projection 1)) raw (numeral 1) inner xs hr
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs) hinner

/-- No native interpretation is used: compose the two existing raw and packed
recurrences, then the original context insertion constructor. -/
theorem actualOriginalLambdaErasureCoordinateSquare :
    OriginalLambdaErasureSquareTargets.ActualOriginalLambdaErasureCoordinateSquare := by
  intro body alpha Delta s out child childOut domain codomain arrow raw childRaw inner
    childRawOut innerOut rawOut erasedType cutoff gamma extended childGamma childExtended
  let A := OriginalLambdaErasureSquareDefinitions.Premises s out child childOut domain codomain arrow
    raw childRaw inner childRawOut innerOut rawOut erasedType cutoff gamma extended childGamma childExtended
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have coords := andLeft h
  have h1 := andRight h
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  have h5 := andRight h4
  have h6 := andRight h5
  have h7 := andRight h6
  have old := rawLambdaAtPairs raw domain childRaw inner
    (andLeft (andRight (andRight coords))) (andLeft (andRight (andRight (andRight coords))))
  have new := rawLambdaAtPairs rawOut domain childRawOut innerOut (andLeft h3) (andLeft h4)
  have rawErase := OriginalRawSyntaxTransportInternalFoldLambdaProof.lambdaBackward .erase
    raw rawOut erasedType cutoff domain childRaw childRawOut old (andLeft h1) new
  have oldPair := andRight (andRight (andRight (andRight coords)))
  have parentPair := OriginalRawSyntaxTransportInternalPackedProof.erasePackedForward
    s out arrow raw rawOut erasedType cutoff oldPair rawErase (andLeft h5)
  have packed := OriginalLambdaConstructorGraphSupportProof.packedAtPairs
    out domain codomain childRawOut arrow innerOut rawOut (andLeft coords) (andLeft h3) (andLeft h4) parentPair
  have ctor := OriginalLambdaConstructorGraphSyntaxProof.constructorBackward
    out domain codomain childOut childRawOut (pairRight childOut codomain childRawOut (andLeft h2)) packed
  have childErase := OriginalRawSyntaxTransportInternalPackedProof.erasePackedBackward
    child childOut codomain childRaw childRawOut erasedType (suc cutoff)
    (andLeft (andRight coords)) (andLeft h1) (andLeft h2)
  have childType := pairLeft childOut codomain childRawOut (andLeft h2)
  have context := OriginalContextInsertionConsProof.consBackward
    erasedType cutoff childGamma childExtended domain gamma extended
    (andLeft h7) (andRight h7) (andLeft h6)
  obtain ⟨result⟩ := andIntro ctor (andIntro childErase (andIntro childType context))
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareProof
