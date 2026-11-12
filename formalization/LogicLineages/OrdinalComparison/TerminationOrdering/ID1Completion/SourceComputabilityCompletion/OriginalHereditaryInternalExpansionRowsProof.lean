module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionBinaryAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem queryUnary (parent child parentRaw rawChild input parameter window gamma W V front suffix joined count index : OTerm alpha)
 (ha2 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) input parameter)))
 (ha1 : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)))
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild index joined))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalHereditaryInternalExpansionChildQueryProof.childCases input parameter _
 intro beta rho Theta first second singleton hrho hfirst hsecond hsingleton
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 have hchildren' := renameInto hchildren rho Theta hrho
 have hdel' := renameInto hdel rho Theta hrho
 have happend' := renameInto happend rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 have hb' := renameInto hb rho Theta hrho
 have hlookup' := renameInto hlookup rho Theta hrho
 have ha2' := renameInto ha2 rho Theta hrho
 have ha1' := renameInto ha1 rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename,numeral,sucRelabel,zRelabel] at hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup' ha2' ha1'
 have hfront := OriginalHereditaryInternalExpansionChildrenProof.unaryCons
   (Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)) (front.relabel rho)
   first ha2' hchildren' hfirst 
 exact OriginalHereditaryInternalExpansionUnaryAppendProof.atUnary
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho)
   (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
   (W.relabel rho) (V.relabel rho) (front.relabel rho) first (suffix.relabel rho)
   (joined.relabel rho) (count.relabel rho) (index.relabel rho)
   hp' hc' hr' hparam' hw' hv' ha1' hfirst hfront hdel' happend' hl' hb' hlookup'

theorem queryBinary (parent child parentRaw rawChild input parameter window gamma W V front suffix joined count index : OTerm alpha)
 (ha2 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) input parameter)))
 (ha1 : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) input)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)))
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild index joined))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalHereditaryInternalExpansionChildQueryProof.childCases input parameter _
 intro beta rho Theta first second singleton hrho hfirst hsecond hsingleton
 simp only [orderRename]
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 have hchildren' := renameInto hchildren rho Theta hrho
 have hdel' := renameInto hdel rho Theta hrho
 have happend' := renameInto happend rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 have hb' := renameInto hb rho Theta hrho
 have hlookup' := renameInto hlookup rho Theta hrho
 have ha2' := renameInto ha2 rho Theta hrho
 have ha1' := renameInto ha1 rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename,numeral,sucRelabel,zRelabel] at hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup' ha2' ha1'
 have hfront := OriginalHereditaryInternalExpansionChildrenProof.binaryCons
   (Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)) (front.relabel rho)
   first second singleton ha2' hchildren' hfirst hsecond hsingleton
 exact OriginalHereditaryInternalExpansionBinaryAppendProof.atBinary
   (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho)
   (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
   (W.relabel rho) (V.relabel rho) (front.relabel rho) first singleton second (suffix.relabel rho)
   (joined.relabel rho) (count.relabel rho) (index.relabel rho)
   hp' hc' hr' hparam' hw' hv' ha1' hfirst hsecond hfront hsingleton hdel' happend' hl' hb' hlookup'

theorem atZero (parent child parentRaw rawChild input parameter window gamma W V front suffix joined count index : OTerm alpha)
 (ha0 : Nonempty (Derivation body Delta (graph2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 0) input parameter)))
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)))
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild index joined))) : Nonempty (Derivation body Delta (ltF V W)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hz := OriginalHereditaryInternalExpansionChildrenProof.otherRow 0 (by decide) (by decide)
   xs front ha0 hchildren
 have he := valueUnique (OriginalRawSyntaxTransport.constant 2 0) front z xs hz (constantValue 0 xs)
 have happ := headTransport InternalApplicationValidityStackAppend.append joined front z
   (Fin.cons suffix Fin.elim0) he happend
 have hfields := OriginalHereditaryInternalFinitePrefixZeroProof.zeroSuffix suffix joined count index rawChild happ hl hlookup
 exact OriginalHereditaryInternalDeletionWeightProof.actualDecrease body alpha Delta
   parent child parentRaw rawChild input parameter suffix count index W V
   hp hr hc hdel hfields.1 hb hfields.2 hw hv

theorem atRows (parent child parentRaw rawChild input parameter window gamma W V front suffix joined count index : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)))
 (hchildren : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front input parameter)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild index joined))) : Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalHereditaryInternalExpansionArityCasesProof.childArityCases input parameter _
 · intro beta rho Theta hrho ha2
   simp only [orderRename]
   have hp' := renameInto hp rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have hr' := renameInto hr rho Theta hrho
   have hparam' := renameInto hparam rho Theta hrho
   have hw' := renameInto hw rho Theta hrho
   have hv' := renameInto hv rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have hdel' := renameInto hdel rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have hl' := renameInto hl rho Theta hrho
   have hb' := renameInto hb rho Theta hrho
   have hlookup' := renameInto hlookup rho Theta hrho
   simp only [graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename] at hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup'
   exact atZero (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho) (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (W.relabel rho) (V.relabel rho) (front.relabel rho) (suffix.relabel rho) (joined.relabel rho) (count.relabel rho) (index.relabel rho) ha2
     hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup'
 · intro beta rho Theta hrho ha2 ha1
   simp only [orderRename]
   have hp' := renameInto hp rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have hr' := renameInto hr rho Theta hrho
   have hparam' := renameInto hparam rho Theta hrho
   have hw' := renameInto hw rho Theta hrho
   have hv' := renameInto hv rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have hdel' := renameInto hdel rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have hl' := renameInto hl rho Theta hrho
   have hb' := renameInto hb rho Theta hrho
   have hlookup' := renameInto hlookup rho Theta hrho
   simp only [graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename] at hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup'
   exact queryUnary (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho) (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (W.relabel rho) (V.relabel rho) (front.relabel rho) (suffix.relabel rho) (joined.relabel rho) (count.relabel rho) (index.relabel rho) ha2 ha1
     hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup'
 · intro beta rho Theta hrho ha2 ha1
   simp only [orderRename]
   have hp' := renameInto hp rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have hr' := renameInto hr rho Theta hrho
   have hparam' := renameInto hparam rho Theta hrho
   have hw' := renameInto hw rho Theta hrho
   have hv' := renameInto hv rho Theta hrho
   have hchildren' := renameInto hchildren rho Theta hrho
   have hdel' := renameInto hdel rho Theta hrho
   have happend' := renameInto happend rho Theta hrho
   have hl' := renameInto hl rho Theta hrho
   have hb' := renameInto hb rho Theta hrho
   have hlookup' := renameInto hlookup rho Theta hrho
   simp only [graph1Rename,graph2Rename,lengthRename,OriginalContextInsertion.Below,orderRename] at hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup'
   exact queryBinary (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho) (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (W.relabel rho) (V.relabel rho) (front.relabel rho) (suffix.relabel rho) (joined.relabel rho) (count.relabel rho) (index.relabel rho) ha2 ha1
     hp' hc' hr' hparam' hw' hv' hchildren' hdel' happend' hl' hb' hlookup'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRowsProof
