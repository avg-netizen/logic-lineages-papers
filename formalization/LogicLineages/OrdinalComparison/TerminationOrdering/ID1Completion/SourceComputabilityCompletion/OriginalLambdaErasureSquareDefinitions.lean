module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal original packed lambda and body coordinates. These are existential
query witnesses in a later consumer, never semantic correctness assumptions. -/
def Coordinates {alpha : Type} (s child domain codomain arrow raw childRaw inner : OTerm alpha) : Formula alpha :=
  graph2 OriginalLambdaConstructor.arrow arrow domain codomain ⊓
    (graph2 InternalPairing.pairing child codomain childRaw ⊓
      (graph2 InternalPairing.pairing inner domain childRaw ⊓
        (graph2 InternalPairing.pairing raw (numeral 1) inner ⊓
          graph2 InternalPairing.pairing s arrow raw)))

/-- Parent and child use the same erased type, but the child cutoff is the
actual successor. The original arbitrary context prefix is retained by Insert. -/
def Premises {alpha : Type}
    (s out child childOut domain codomain arrow raw childRaw inner childRawOut innerOut rawOut
      erasedType cutoff gamma extended childGamma childExtended : OTerm alpha) : Formula alpha :=
  Coordinates s child domain codomain arrow raw childRaw inner ⊓
    (graph3 OriginalRawSyntaxTransport.eraseRaw childRawOut erasedType (suc cutoff) childRaw ⊓
      (graph2 InternalPairing.pairing childOut codomain childRawOut ⊓
        (graph2 InternalPairing.pairing innerOut domain childRawOut ⊓
          (graph2 InternalPairing.pairing rawOut (numeral 1) innerOut ⊓
            (graph3 OriginalRawSyntaxTransport.erasePackedRaw out erasedType cutoff s ⊓
              (OriginalContextInsertion.Insert erasedType cutoff gamma extended ⊓
                (graph2 InternalListCodec.consCode childGamma domain gamma ⊓
                  graph2 InternalListCodec.consCode childExtended domain extended)))))))

def Result {alpha : Type}
    (out child childOut domain codomain erasedType cutoff childGamma childExtended : OTerm alpha) : Formula alpha :=
  graph3 OriginalLambdaConstructor.constructor out domain codomain childOut ⊓
    (graph3 OriginalRawSyntaxTransport.erasePackedRaw childOut erasedType (suc cutoff) child ⊓
      (graph1 InternalUnpair.left codomain childOut ⊓
        OriginalContextInsertion.Insert erasedType (suc cutoff) childGamma childExtended))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDefinitions
