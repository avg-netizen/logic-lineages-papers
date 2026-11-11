module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalInternalApplicationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationBackward (leaf : Program 2)
    (value d e fn arg parameter fOut aOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hfn : Nonempty (Derivation positive Delta (graph2 (fold leaf) fOut fn parameter)))
    (ha : Nonempty (Derivation positive Delta (graph2 (fold leaf) aOut arg parameter)))
    (hr : Nonempty (Derivation positive Delta (graph4 application out d e fOut aOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons value Fin.elim0) _
  intro beta j Theta payload hj hp
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hp
  have hf' := renameInto hf j Theta hj
  have hfn' := renameInto hfn j Theta hj
  have ha' := renameInto ha j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [applicationFieldsRename] at hf'
  rw [graph2Rename] at hfn' ha'
  rw [graph4Rename] at hr'
  exact atRootPayload leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) payload (fOut.relabel j) (aOut.relabel j) (out.relabel j) hf' hp hfn' ha' hr'

theorem applicationForward (leaf : Program 2)
    (value d e fn arg parameter fOut aOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hfn : Nonempty (Derivation positive Delta (graph2 (fold leaf) fOut fn parameter)))
    (ha : Nonempty (Derivation positive Delta (graph2 (fold leaf) aOut arg parameter)))
    (ho : Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter))) :
    Nonempty (Derivation positive Delta (graph4 application out d e fOut aOut)) := by
  apply programCases application (Fin.cons d (Fin.cons e (Fin.cons fOut (Fin.cons aOut Fin.elim0)))) _
  intro beta j Theta produced hj hp
  rw [graph4Rename]
  simp only [consTermRename,emptyRename] at hp
  have hf' := renameInto hf j Theta hj
  have hfn' := renameInto hfn j Theta hj
  have ha' := renameInto ha j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [applicationFieldsRename] at hf'
  rw [graph2Rename] at hfn' ha' ho'
  have hfold := applicationBackward leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j)
    (arg.relabel j) (parameter.relabel j) (fOut.relabel j) (aOut.relabel j) produced hf' hfn' ha' hp
  exact outputTransport application produced (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (fOut.relabel j) (Fin.cons (aOut.relabel j) Fin.elim0))))
    (valueUnique (fold leaf) produced (out.relabel j)
      (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hfold ho') hp

theorem actualOriginalLambdaTraversalInternalApplication :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalApplication := by
  intro positive leaf alpha Delta value d e fn arg fOut aOut out parameter
  let C := ApplicationFields value d e fn arg ⊓
    (graph2 (fold leaf) fOut fn parameter ⊓ graph2 (fold leaf) aOut arg parameter)
  let G := graph2 (fold leaf) out value parameter
  let R := graph4 application out d e fOut aOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := applicationForward leaf value d e fn arg parameter fOut aOut out
    (andLeft hcG) (andLeft (andRight hcG)) (andRight (andRight hcG)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := applicationBackward leaf value d e fn arg parameter fOut aOut out
    (andLeft hcR) (andLeft (andRight hcR)) (andRight (andRight hcR)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
