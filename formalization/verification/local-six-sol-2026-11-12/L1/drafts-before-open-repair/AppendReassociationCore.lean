module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof (consTermRename emptyRename)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open AppendReassociationSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroCore (a b c ab bc out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z a b c ab bc out))) :
 Nonempty (Derivation body Delta (result a bc out)) := by
 have ha := lengthZeroRecover a (andLeft hf)
 have hab := headTransport InternalApplicationValidityStackAppend.append ab a z (Fin.cons b Fin.elim0)
   ha (andLeft (andRight hf))
 have he := InternalApplicationValidityStackAppendListProof.appendZeroRecover ab b hab
 have hout := headTransport InternalApplicationValidityStackAppend.append out ab b (Fin.cons c Fin.elim0)
   he (andRight (andRight (andRight hf)))
 have ho := valueUnique InternalApplicationValidityStackAppend.append bc out (Fin.cons b (Fin.cons c Fin.elim0))
   (andLeft (andRight (andRight hf))) hout
 have hz := outputTransport InternalApplicationValidityStackAppend.append bc out (Fin.cons z (Fin.cons bc Fin.elim0))
   ho (InternalApplicationValidityStackAppendListProof.appendZeroValue bc)
 obtain ⟨ha⟩ := ha
 exact headTransport InternalApplicationValidityStackAppend.append out z a (Fin.cons bc Fin.elim0) ⟨symm ha⟩ hz

theorem atCons (count a b c ab bc out head tail : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) a b c ab bc out)))
 (hc : Nonempty (Derivation body Delta (consGraph a head tail))) :
 Nonempty (Derivation body Delta (result a bc out)) := by
 apply InternalAcceptanceSupportProof.programCases InternalApplicationValidityStackAppend.append
   (Fin.cons tail (Fin.cons b Fin.elim0)) _
 intro beta j Theta tailAB hinc htab
 simp only [consTermRename,emptyRename] at htab
 have hi' := renameInto hi j Theta hinc
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hinc
 simp only [fieldsRename,sucRelabel] at hf'
 have hc' := renameInto hc j Theta hinc
 rw [consGraphRename] at hc'
 apply InternalAcceptanceSupportProof.programCases InternalApplicationValidityStackAppend.append
   (Fin.cons tailAB (Fin.cons (c.relabel j) Fin.elim0)) _
 intro gamma k Xi tailOut hk hto
 simp only [consTermRename,emptyRename] at hto
 have hi'' := renameInto hi' k Xi hk
 rw [rowRename] at hi''
 have hf'' := renameInto hf' k Xi hk
 simp only [fieldsRename,sucRelabel] at hf''
 have hc'' := renameInto hc' k Xi hk
 rw [consGraphRename] at hc''
 have htab' := renameInto htab k Xi hk
 rw [graph2Rename] at htab'
 have hab := InternalApplicationValidityStackAppendListProof.consForward
   ((a.relabel j).relabel k) ((head.relabel j).relabel k) ((tail.relabel j).relabel k)
   ((b.relabel j).relabel k) (tailAB.relabel k) ((ab.relabel j).relabel k) hc'' htab' (andLeft (andRight hf''))
 have hout := InternalApplicationValidityStackAppendListProof.consForward
   ((ab.relabel j).relabel k) ((head.relabel j).relabel k) (tailAB.relabel k)
   ((c.relabel j).relabel k) tailOut ((out.relabel j).relabel k) hab hto (andRight (andRight (andRight hf'')))
 have hlen := OriginalContextInsertionSupportProof.successorLengthTail
   ((a.relabel j).relabel k) ((head.relabel j).relabel k) ((tail.relabel j).relabel k)
   ((count.relabel j).relabel k) hc'' (andLeft hf'')
 have hrec := rowApply ((count.relabel j).relabel k) ((tail.relabel j).relabel k)
   ((b.relabel j).relabel k) ((c.relabel j).relabel k) (tailAB.relabel k) ((bc.relabel j).relabel k) tailOut hi''
   (andIntro hlen (andIntro htab' (andIntro (andLeft (andRight (andRight hf''))) hto)))
 simp only [resultRename]
 exact InternalApplicationValidityStackAppendListProof.consBackward
   ((a.relabel j).relabel k) ((head.relabel j).relabel k) ((tail.relabel j).relabel k)
   ((bc.relabel j).relabel k) tailOut ((out.relabel j).relabel k) hc'' hrec hout

theorem succCore (count a b c ab bc out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) a b c ab bc out))) :
 Nonempty (Derivation body Delta (result a bc out)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases a _
   (OriginalContextInsertionSupportProof.successorLengthNonzero count a (andLeft hf))
 intro beta j Theta head tail hinc hc
 have hi' := renameInto hi j Theta hinc
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hinc
 simp only [fieldsRename,sucRelabel] at hf'
 rw [resultRename]
 exact atCons (count.relabel j) (a.relabel j) (b.relabel j) (c.relabel j)
   (ab.relabel j) (bc.relabel j) (out.relabel j) head tail hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationCore
