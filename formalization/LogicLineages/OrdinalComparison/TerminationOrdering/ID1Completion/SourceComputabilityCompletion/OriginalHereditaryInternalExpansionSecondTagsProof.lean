module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondTagsProof
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

theorem applicationTagSecond (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases input _ ht
 intro beta rho Theta domain fn arg hrho hctor
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hjob' := renameInto hjob rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,graph2Rename] at hp' hc' hr' hparam' hjob' hw' hv'
 exact OriginalHereditaryInternalExpansionSecondProof.applicationSecond
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (childRaw.relabel rho)
   (input.relabel rho) domain fn arg (parameter.relabel rho) (window.relabel rho)
   (gamma.relabel rho) (W.relabel rho) (V.relabel rho) hctor hp' hc' hr' hparam' hjob' hw' hv'

theorem consTagSecond (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases input _ ht
 intro beta rho Theta typ head tail hrho hctor
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hjob' := renameInto hjob rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,graph2Rename] at hp' hc' hr' hparam' hjob' hw' hv'
 exact OriginalHereditaryInternalExpansionSecondProof.consSecond
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (childRaw.relabel rho)
   (input.relabel rho) typ head tail (parameter.relabel rho) (window.relabel rho)
   (gamma.relabel rho) (W.relabel rho) (V.relabel rho) hctor hp' hc' hr' hparam' hjob' hw' hv'

theorem numberedTagSecond (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases input _ ht
 intro beta rho Theta label head typ base types extras hrho hctor
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hjob' := renameInto hjob rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [graph1Rename,graph2Rename] at hp' hc' hr' hparam' hjob' hw' hv'
 exact OriginalHereditaryInternalExpansionSecondProof.numberedSecond
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (childRaw.relabel rho)
   (input.relabel rho) label head typ base types extras (parameter.relabel rho) (window.relabel rho)
   (gamma.relabel rho) (W.relabel rho) (V.relabel rho) hctor hp' hc' hr' hparam' hjob' hw' hv'

/-- All-raw arity-two dispatch, using actual parser reconstruction rather
than any native decoding or source-validity assumption. -/
theorem rawSecond (parent child parentRaw childRaw input parameter window gamma W V : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRaw child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hjob : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob childRaw input parameter)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply orCases (arityTwoTags input ha)
 · intro Theta inc ht
   exact applicationTagSecond parent child parentRaw childRaw input parameter window gamma W V ht
     (weakenProof hp inc) (weakenProof hc inc) (weakenProof hr inc) (weakenProof hparam inc)
     (weakenProof hjob inc) (weakenProof hw inc) (weakenProof hv inc)
 · intro Theta inc ht
   apply orCases ht
   · intro Xi inc2 ht2
     exact numberedTagSecond parent child parentRaw childRaw input parameter window gamma W V ht2
       (weakenProof (weakenProof hp inc) inc2) (weakenProof (weakenProof hc inc) inc2)
       (weakenProof (weakenProof hr inc) inc2) (weakenProof (weakenProof hparam inc) inc2)
       (weakenProof (weakenProof hjob inc) inc2) (weakenProof (weakenProof hw inc) inc2)
       (weakenProof (weakenProof hv inc) inc2)
   · intro Xi inc2 ht2
     exact consTagSecond parent child parentRaw childRaw input parameter window gamma W V ht2
       (weakenProof (weakenProof hp inc) inc2) (weakenProof (weakenProof hc inc) inc2)
       (weakenProof (weakenProof hr inc) inc2) (weakenProof (weakenProof hparam inc) inc2)
       (weakenProof (weakenProof hjob inc) inc2) (weakenProof (weakenProof hw inc) inc2)
       (weakenProof (weakenProof hv inc) inc2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondTagsProof
