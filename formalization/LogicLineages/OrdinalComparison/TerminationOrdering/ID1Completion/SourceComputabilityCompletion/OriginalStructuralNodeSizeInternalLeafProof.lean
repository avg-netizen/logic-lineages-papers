module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalStructuralNodeSizeInternalMachineCompletionLeafProof
open OriginalStructuralNodeSizeInternalMachineCompletionRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawFromFold (input out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (graph3 OriginalStructuralNodeSizeInternalMachineCompletion.fold out z z input))) :
    Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw out input)) := by
  apply programCases OriginalStructuralNodeSize.run (Fin.cons z (Fin.cons z (Fin.cons input Fin.elim0))) _
  intro beta j Theta state hj hs
  rw [graph1Rename]
  simp only [consTermRename,emptyRename,zRelabel] at hs
  have hf' := renameInto hf j Theta hj
  simp only [graph3Rename,zRelabel] at hf'
  let xs : Fin 1 → OTerm beta := Fin.cons (input.relabel j) Fin.elim0
  have inner := compositionValue OriginalStructuralNodeSize.run
    ![constant 1 0,constant 1 0,.projection 0] state xs
    ![z,z,input.relabel j] hs
    (fun i => Fin.cases (constantValue 0 xs) (Fin.cases (constantValue 0 xs)
      (Fin.cases (projectionValue 0 xs) (fun k => Fin.elim0 k))) i)
  have hout := unaryRecover output OriginalStructuralNodeSize.run (out.relabel j) state
    ![z,z,input.relabel j] hf' hs
  exact unaryValue output (.composition OriginalStructuralNodeSize.run ![constant 1 0,constant 1 0,.projection 0])
    (out.relabel j) state xs hout inner

theorem leaf (input : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) z input))) :
    Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw (suc z) input)) :=
  rawFromFold input (suc z) (completionFold z z input (suc z) (suc z) (leafBound input)
    (leafComplete z z input (suc z) ha (constantValue 1 ![z,z,input])))

theorem actualInternalLeaf : OriginalStructuralNodeSizeTargets.InternalLeaf := by
  intro body alpha Delta input
  obtain ⟨h⟩ := leaf (body := body) (Delta := graph1 (arityOf (.projection 0)) z input :: Delta)
    input ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalLeafProof
