module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFirstTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSecondTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionBinaryAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atBinary (parent child parentRaw rawChild input parameter window gamma W V
 front first middle second suffix joined count index : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawChild child)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) input)))
 (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first input parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second input parameter)))
 (hfront : Nonempty (Derivation body Delta (consGraph front first middle)))
 (htail : Nonempty (Derivation body Delta (consGraph middle second z)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix input parameter)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count joined)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild index joined))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 apply OriginalHereditaryInternalFinitePrefixCasesProof.binaryCases body alpha Delta
   front first middle second suffix joined count index rawChild _
   hfront htail happend hl hb hlookup
 · intro beta rho Theta hrho he
   simp only [orderRename]
   have hp' := renameInto hp rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have hr' := renameInto hr rho Theta hrho
   have hparam' := renameInto hparam rho Theta hrho
   have hw' := renameInto hw rho Theta hrho
   have hv' := renameInto hv rho Theta hrho
   have ha' := renameInto ha rho Theta hrho
   have hf' := renameInto hf rho Theta hrho
   simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hp' hc' hr' hparam' hw' hv' ha' hf'
   obtain ⟨he⟩ := he
   have hjob := outputTransport OriginalHereditaryExpansion.firstJob (first.relabel rho) (rawChild.relabel rho)
     (Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)) ⟨symm he⟩ hf'
   exact OriginalHereditaryInternalExpansionFirstTagsProof.rawFirstBinary
     (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho)
     (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
     (W.relabel rho) (V.relabel rho) ha' hp' hc' hr' hparam' hjob hw' hv'
 · intro beta rho Theta hrho he
   simp only [orderRename]
   have hp' := renameInto hp rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have hr' := renameInto hr rho Theta hrho
   have hparam' := renameInto hparam rho Theta hrho
   have hw' := renameInto hw rho Theta hrho
   have hv' := renameInto hv rho Theta hrho
   have ha' := renameInto ha rho Theta hrho
   have hs' := renameInto hs rho Theta hrho
   simp only [graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel] at hp' hc' hr' hparam' hw' hv' ha' hs'
   obtain ⟨he⟩ := he
   have hjob := outputTransport OriginalHereditaryExpansion.secondJob (second.relabel rho) (rawChild.relabel rho)
     (Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)) ⟨symm he⟩ hs'
   exact OriginalHereditaryInternalExpansionSecondTagsProof.rawSecond
     (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho)
     (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
     (W.relabel rho) (V.relabel rho) ha' hp' hc' hr' hparam' hjob hw' hv'
 · intro beta rho Theta cutoff length hrho hlen hbound hlook
   simp only [orderRename]
   have hp' := renameInto hp rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have hr' := renameInto hr rho Theta hrho
   have hw' := renameInto hw rho Theta hrho
   have hv' := renameInto hv rho Theta hrho
   have hdel' := renameInto hdel rho Theta hrho
   simp only [graph1Rename,graph2Rename] at hp' hc' hr' hw' hv' hdel'
   exact OriginalHereditaryInternalDeletionWeightProof.actualDecrease body beta Theta
     (parent.relabel rho) (child.relabel rho) (parentRaw.relabel rho) (rawChild.relabel rho)
     (input.relabel rho) (parameter.relabel rho) (suffix.relabel rho) length cutoff
     (W.relabel rho) (V.relabel rho) hp' hr' hc' hdel' hlen hbound hlook hw' hv'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionBinaryAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionBinaryAppendProof
