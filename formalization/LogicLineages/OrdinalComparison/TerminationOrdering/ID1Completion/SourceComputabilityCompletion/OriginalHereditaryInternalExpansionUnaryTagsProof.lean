module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalOriginalOrderSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaTagFirst (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases input _ ht
 intro beta rho Theta domain term hrho hctor
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hjob' := renameInto hjob rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,graph2Rename] at hp' hc' hr' hparam' hjob' hw' hv'
 exact OriginalHereditaryInternalExpansionLambdaProof.lambdaFirst
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (childRaw.relabel rho)
   (input.relabel rho) domain term (parameter.relabel rho) (window.relabel rho)
   (gamma.relabel rho) (W.relabel rho) (V.relabel rho) hctor hp' hc' hr' hparam' hjob' hw' hv'

theorem ordinaryTagFirst (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases input _ ht
 intro beta rho Theta head base hrho hctor
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hjob' := renameInto hjob rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,graph2Rename] at hp' hc' hr' hparam' hjob' hw' hv'
 exact OriginalHereditaryInternalExpansionOrdinaryProof.ordinaryFirst
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (childRaw.relabel rho)
   (input.relabel rho) head base (parameter.relabel rho) (window.relabel rho)
   (gamma.relabel rho) (W.relabel rho) (V.relabel rho) hctor hp' hc' hr' hparam' hjob' hw' hv'

theorem rawFirstUnary (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply orCases (arityOneTags input ha)
 · intro Theta inc ht
   exact lambdaTagFirst parent child parentRaw childRaw input parameter window gamma W V ht
     (weakenProof hp inc) (weakenProof hc inc) (weakenProof hr inc) (weakenProof hparam inc)
     (weakenProof hjob inc) (weakenProof hw inc) (weakenProof hv inc)
 · intro Theta inc ht
   exact ordinaryTagFirst parent child parentRaw childRaw input parameter window gamma W V ht
     (weakenProof hp inc) (weakenProof hc inc) (weakenProof hr inc) (weakenProof hparam inc)
     (weakenProof hjob inc) (weakenProof hw inc) (weakenProof hv inc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryTagsProof
