module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEquationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalParameterizedCanonicalResultFoldSyntaxProof (foldGraphRename applicationGraphRename)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalApplicationSidecar OriginalNeutralApplication OriginalNeutralApplicationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Bind the rebuilt application internally and use the actual final leaf's
derived identity. Neither N(function) nor a second parent fold is introduced. -/
theorem forward (data : Data) (window : Program 1)
    (arrow d e function argument out argumentOut parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window)
        argumentOut argument parameter)))
    (hj : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph
        (selectedData data window) out d e function argument parameter))) :
    Nonempty (Derivation body Gamma (graph4 application out d e function argumentOut)) := by
  apply programCases application
    (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argumentOut Fin.elim0)))) _
  intro beta j Delta rebuilt hin hr
  rw [graph4Rename]
  have hp' := renameInto hp j Delta hin
  have hn' := renameInto hn j Delta hin
  have hj' := renameInto hj j Delta hin
  rw [inputPremisesRename] at hp'
  rw [foldGraphRename] at hn'
  rw [applicationGraphRename] at hj'
  simp only [consTermRename,emptyRename] at hr
  exact OriginalNeutralApplicationValueProof.forwardAtRaw data window
    (arrow.relabel j) (d.relabel j) (e.relabel j) (function.relabel j)
    (argument.relabel j) (out.relabel j) (argumentOut.relabel j) rebuilt (parameter.relabel j)
    hp' hn' hr hj'

theorem backward (data : Data) (window : Program 1)
    (arrow d e function argument out argumentOut parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window)
        argumentOut argument parameter)))
    (hr : Nonempty (Derivation body Gamma (graph4 application out d e function argumentOut))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph
        (selectedData data window) out d e function argument parameter)) :=
  OriginalNeutralApplicationValueProof.backward data window
    arrow d e function argument out argumentOut parameter hp hn hr

theorem equation (data : Data) (window : Program 1)
    (arrow d e function argument out argumentOut parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hn : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window)
        argumentOut argument parameter))) :
    Nonempty (Derivation body Gamma
      ((InternalParameterizedCanonicalResultFold.applicationGraph
          (selectedData data window) out d e function argument parameter).iff
        (graph4 application out d e function argumentOut))) := by
  let J := InternalParameterizedCanonicalResultFold.applicationGraph
    (selectedData data window) out d e function argument parameter
  let A := graph4 application out d e function argumentOut
  have hj : Nonempty (Derivation body (J :: Gamma) J) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hforward⟩ := forward data window arrow d e function argument out argumentOut parameter
    (withHyp hp J) (withHyp hn J) hj
  obtain ⟨hbackward⟩ := backward data window arrow d e function argument out argumentOut parameter
    (withHyp hp A) (withHyp hn A) ha
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hforward)
    (Derivation.implicationIntroduction hbackward)⟩

theorem actualOriginalTypedApplicationEquation :
    OriginalNeutralApplicationTargets.ActualOriginalTypedApplicationEquation := by
  intro body data window alpha Gamma arrow d e function argument out argumentOut parameter
  let P := InputPremises (selectedData data window) window arrow d e function argument parameter ⊓
    InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut argument parameter
  have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := equation data window arrow d e function argument out argumentOut parameter
    (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEquationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEquationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEquationProof.actualOriginalTypedApplicationEquation
