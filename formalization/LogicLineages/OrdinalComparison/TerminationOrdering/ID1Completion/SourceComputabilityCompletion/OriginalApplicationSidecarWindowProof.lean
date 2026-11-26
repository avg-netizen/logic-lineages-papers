module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the actual unary window graph through the first composition,
then reintroduce that SAME graph through the other projection vector. -/
theorem transferAtContext (window : Program 1)
    (value input other parameter context : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left context parameter)))
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) value input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) value other parameter)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  let ys : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons other (Fin.cons parameter Fin.elim0)
  have hx := unaryValue InternalUnpair.left (.projection 1) context parameter xs hc (projectionValue 1 xs)
  have hy := unaryValue InternalUnpair.left (.projection 1) context parameter ys hc (projectionValue 1 ys)
  have hwindow := unaryRecover window (leftOf (.projection 1)) value context xs hw hx
  exact unaryValue window (leftOf (.projection 1)) value context ys hwindow hy

/-- The context witness is supplied and eliminated by original internal
Program totality. No semantic value or native graph reflection occurs. -/
theorem windowTransfer (window : Program 1)
    (value input other parameter : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) value input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) value other parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons parameter Fin.elim0) _
  intro beta j Theta context hj hc
  simp only [graph2Rename]
  have hw' := renameInto hw j Theta hj
  simp only [graph2Rename] at hw'
  simp only [consTermRename,emptyRename] at hc
  exact transferAtContext window (value.relabel j) (input.relabel j) (other.relabel j)
    (parameter.relabel j) context hc hw'

theorem actualOriginalApplicationSidecarWindowIndependence :
    OriginalApplicationSidecarTargets.ActualOriginalApplicationSidecarWindowIndependence := by
  intro body alpha Delta window input other parameter
  let A := OriginalFunctionNeutrality.windowGraph window input parameter
  let B := OriginalFunctionNeutrality.windowGraph window other parameter
  obtain ⟨forward⟩ := windowTransfer (body := body) (Delta := A :: Delta)
    window InternalOriginalStepGuard.one input other parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := windowTransfer (body := body) (Delta := B :: Delta)
    window InternalOriginalStepGuard.one other input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof.actualOriginalApplicationSidecarWindowIndependence
