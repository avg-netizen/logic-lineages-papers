module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem mapAt (xs : Fin 7 → OTerm alpha) (out range : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.variableBranch out xs)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range (xs 4)))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalRawSyntaxTransport.variableConstructor) out range)) :=
  unaryRecover (InternalListMap.map OriginalRawSyntaxTransport.variableConstructor)
    (.composition OriginalAscendingRange.range ![.projection 4]) out range xs hg
    (by
      have hv := unaryValue OriginalAscendingRange.range (.projection 4) range (xs 4) xs hr (projectionValue 4 xs)
      have he : (fun _ : Fin 1 => (ComputabilityKnowledge.GorbowPRProgram.Program.projection 4 : ComputabilityKnowledge.GorbowPRProgram.Program 7)) = ![.projection 4] := by
        funext i
        fin_cases i
        rfl
      rw [he] at hv
      exact hv)

theorem forwardAt (vb out code range : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalRawSyntaxTransport.variableConstructor) out range)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range vb)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.variableCase vb code)) := by
  have hi := MapElimProof.recover OriginalRawSyntaxTransport.variableConstructor range out code hg hm
  apply MapImageEliminationProof.cases OriginalRawSyntaxTransport.variableConstructor range code _ hi
  intro beta j Theta index hj hmem hctor
  rw [VariableSyntaxProof.caseRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph1Rename] at hrj
  have hb := (OriginalAscendingRange.StatementChecks.exactMembership body beta Theta
    (vb.relabel j) (range.relabel j) index hrj).mp hmem
  exact VariableSyntaxProof.introduce (vb.relabel j) (code.relabel j) ![index] (andIntro hb hctor)

theorem backwardAt (vb out code range : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalRawSyntaxTransport.variableConstructor) out range)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalAscendingRange.range range vb)))
    (hw : Nonempty (Derivation body Delta (Targets.variableCase vb code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply VariableSyntaxProof.cases vb code _ hw
  intro beta j Theta ys hj hf
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph1Rename] at hrj
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [graph1Rename] at hgj
  have hmem := (OriginalAscendingRange.StatementChecks.exactMembership body beta Theta
    (vb.relabel j) (range.relabel j) (ys 0) hrj).mpr (andLeft hf)
  exact MapIntroProof.introduce OriginalRawSyntaxTransport.variableConstructor
    (range.relabel j) z (out.relabel j) (code.relabel j) z (ys 0) hgj hmem (andRight hf)

theorem forward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.variableBranch out xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.variableCase (xs 4) code)) := by
  apply programCases OriginalAscendingRange.range (Fin.cons (xs 4) Fin.elim0) _
  intro beta j Theta range hj hr
  simp only [consTermRename,emptyRename] at hr
  rw [VariableSyntaxProof.caseRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact forwardAt ((xs 4).relabel j) (out.relabel j) (code.relabel j) range
    (mapAt (fun i => (xs i).relabel j) (out.relabel j) range hgj hr) hr hmj

theorem backward (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph OriginalEnumerationConstructorLayer.variableBranch out xs)))
    (hw : Nonempty (Derivation body Delta (Targets.variableCase (xs 4) code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply programCases OriginalAscendingRange.range (Fin.cons (xs 4) Fin.elim0) _
  intro beta j Theta range hj hr
  simp only [consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  rw [VariableSyntaxProof.caseRename] at hwj
  exact backwardAt ((xs 4).relabel j) (out.relabel j) (code.relabel j) range
    (mapAt (fun i => (xs i).relabel j) (out.relabel j) range hgj hr) hr hwj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
