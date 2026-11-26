module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEquationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalParameterizedCanonicalResultFoldSyntaxProof (foldGraphRename applicationGraphRename)
open OriginalApplicationSidecar OriginalNeutralApplication OriginalNeutralApplicationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original raw argument's actual full-fold value is obtained and
eliminated internally. The requested function is never replaced by a fold. -/
theorem eliminate (data : Data) (window : Program 1)
    (arrow d e function argument out parameter : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Gamma
      (InputPremises (selectedData data window) window arrow d e function argument parameter)))
    (hj : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph
        (selectedData data window) out d e function argument parameter)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
      (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
      ∀ argumentOut : OTerm beta,
      Nonempty (Derivation body Delta
        (Recovered (selectedData data window) (d.relabel j) (e.relabel j) (function.relabel j)
          (argument.relabel j) (out.relabel j) argumentOut (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply programCases (InternalParameterizedCanonicalResultFold.foldN (selectedData data window))
    (Fin.cons argument (Fin.cons parameter Fin.elim0)) psi
  intro beta j Delta argumentOut hin hn
  have hp' := renameInto hp j Delta hin
  have hj' := renameInto hj j Delta hin
  rw [inputPremisesRename] at hp'
  rw [applicationGraphRename] at hj'
  simp only [consTermRename,emptyRename] at hn
  have hr := OriginalNeutralApplicationEquationProof.forward data window
    (arrow.relabel j) (d.relabel j) (e.relabel j) (function.relabel j)
    (argument.relabel j) (out.relabel j) argumentOut (parameter.relabel j) hp' hn hj'
  exact next beta j Delta hin argumentOut (andIntro hn hr)

theorem actualOriginalTypedApplicationElimination :
    OriginalNeutralApplicationTargets.ActualOriginalTypedApplicationElimination := by
  intro body data window alpha Gamma arrow d e function argument out parameter psi
  dsimp only
  intro hp hj next
  exact eliminate data window arrow d e function argument out parameter psi hp hj next

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEliminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEliminationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEliminationProof.actualOriginalTypedApplicationElimination
