module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename)
open InternalApplicationStepPeelSupportProof (andLeft andRight queryCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalComputabilityDownwardSyntaxProof (certificateRename)
open GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveSourceExposureTargets PositiveSourceExposureSyntaxProof PositiveSourceExposureQueries
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Program totality binds ALL original coordinates inside the derivation.
The output existential block retains those SAME witnesses and suffix. -/
theorem expose (q : GlobalSourcePackage.Inputs) (context : Nat) (f g path : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 q.window (numeral 1) (numeral context))))
    (hc : Nonempty (Derivation body Delta
      (InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false context f g path))) :
    Nonempty (Derivation body Delta (Witness q context f g path)) := by
  let xs : Fin 4 → OTerm alpha := ![f,g,path,numeral context]
  apply queryCases queries xs _
  intro beta j ys Theta hj hq
  rw [witnessRename]
  have hw' := renameInto hw j Theta hj
  simp only [graph1Rename,numeralRename] at hw'
  have hc' := renameInto hc j Theta hj
  rw [certificateRename] at hc'
  have hx : (fun i => (xs i).relabel j) =
      (![f.relabel j,g.relabel j,path.relabel j,numeral context] : Fin 4 → OTerm beta) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases (numeralRename context j) (fun k => Fin.elim0 k)))) i
  rw [hx] at hq
  exact witnessIntro q context (f.relabel j) (g.relabel j) (path.relabel j) ys
    (PositiveSourceExposureCoreProof.atQueries q context (f.relabel j) (g.relabel j)
      (path.relabel j) ys hw' hc' hq)

theorem actualOriginalPositiveFirstRawStep : ActualOriginalPositiveFirstRawStep := by
  intro p H G W P body alpha Delta context f g path
  let q := Integration.preparedKernelFinalInputs p H G W P
  let A := graph1 q.window (numeral 1) (numeral context) ⊓
    InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false context f g path
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := expose q context f g path (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureProof
