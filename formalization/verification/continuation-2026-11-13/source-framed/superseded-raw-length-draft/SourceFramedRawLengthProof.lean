module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnShapeCompletion
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm trans congSuc)
open InternalAdditionLawsProof (add leftZero leftSuccessor)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryInternalExpansionLengthRowsProof (unaryLength binaryLength)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof (arityValueAt)
open UniformReturnShapeCompletion (weakenInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atChildren (raw parameter front suffix out count children first second middle : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hf : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob first raw parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob second raw parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode middle second z)))
 (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count suffix)))
 : Nonempty (Derivation body Delta (lengthGraph (add children count) out)) := by
 apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.arityGraphCases raw children _ ha
 · intro Theta hi hn
   have ha' := weakenInto ha Theta hi
   have hf' := weakenInto hf Theta hi
   have hs' := weakenInto hs Theta hi
   have hm' := weakenInto hm Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hl' := weakenInto hl Theta hi
   have he := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children z
     (Fin.cons raw Fin.elim0) ha' hn
   let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
   have hn2 := arityValueAt (.projection 0) z raw xs (projectionValue 0 xs) hn
   have hz := OriginalHereditaryInternalExpansionChildrenProof.otherRow 0 (by decide) (by decide) xs front hn2 hc'
   have hfront := valueUnique (OriginalRawSyntaxTransport.constant 2 0) front z xs hz (constantValue 0 xs)
   have hpzero := headTransport InternalApplicationValidityStackAppend.append out front z
     (Fin.cons suffix Fin.elim0) hfront hp'
   obtain ⟨hout⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover out suffix hpzero
   have hlen := headTransport length count suffix out Fin.elim0 ⟨symm hout⟩ hl'
   obtain ⟨he⟩ := he
   exact outputTransport length count (add children count) (Fin.cons out Fin.elim0)
     ⟨trans (symm (leftZero count)) (InternalOriginalOrderProof.congAddRight count (symm he))⟩ hlen
 · intro Theta hi hn
   have ha' := weakenInto ha Theta hi
   have hf' := weakenInto hf Theta hi
   have hs' := weakenInto hs Theta hi
   have hm' := weakenInto hm Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hl' := weakenInto hl Theta hi
   have he := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children (suc z)
     (Fin.cons raw Fin.elim0) ha' hn
   let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
   have hn2 := arityValueAt (.projection 0) (suc z) raw xs (projectionValue 0 xs) hn
   have hcons := OriginalHereditaryInternalExpansionChildrenProof.unaryCons xs front first hn2 hc' hf'
   have hlen := unaryLength front first suffix out count hcons hp' hl'
   obtain ⟨he⟩ := he
   exact outputTransport length (suc count) (add children count) (Fin.cons out Fin.elim0)
     ⟨trans (symm (trans (leftSuccessor z count) (congSuc (leftZero count)))) (InternalOriginalOrderProof.congAddRight count (symm he))⟩ hlen
 · intro Theta hi hn
   have ha' := weakenInto ha Theta hi
   have hf' := weakenInto hf Theta hi
   have hs' := weakenInto hs Theta hi
   have hm' := weakenInto hm Theta hi
   have hc' := weakenInto hc Theta hi
   have hp' := weakenInto hp Theta hi
   have hl' := weakenInto hl Theta hi
   have he := valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) children (suc (suc z))
     (Fin.cons raw Fin.elim0) ha' hn
   let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
   have hn2 := arityValueAt (.projection 0) (suc (suc z)) raw xs (projectionValue 0 xs) hn
   have hcons := OriginalHereditaryInternalExpansionChildrenProof.binaryCons xs front first second middle hn2 hc' hf' hs' hm'
   have hlen := binaryLength front first middle second suffix out count hcons hm' hp' hl'
   obtain ⟨he⟩ := he
   exact outputTransport length (suc (suc count)) (add children count) (Fin.cons out Fin.elim0)
     ⟨trans (symm (trans (leftSuccessor (suc z) count) (congSuc (trans (leftSuccessor z count) (congSuc (leftZero count)))))) (InternalOriginalOrderProof.congAddRight count (symm he))⟩ hlen
theorem rowsLength (raw parameter front suffix out count children : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count suffix))) :
 Nonempty (Derivation body Delta (lengthGraph (add children count) out)) := by
 apply OriginalHereditaryInternalExpansionChildQueryProof.childCases raw parameter _
 intro beta j Theta first second middle hi hf hs hm
 have ha' := renameInto ha j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hl' := renameInto hl j Theta hi
 simp only [graph1Rename,graph2Rename,lengthRename] at ha' hc' hp' hl'
 simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
 exact atChildren (raw.relabel j) (parameter.relabel j) (front.relabel j) (suffix.relabel j)
   (out.relabel j) (count.relabel j) (children.relabel j) first second middle ha' hf hs hm hc' hp' hl'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawLengthProof
