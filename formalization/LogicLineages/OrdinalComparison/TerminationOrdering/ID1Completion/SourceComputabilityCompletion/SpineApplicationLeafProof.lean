module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalTagArithmeticSyntaxProof (OTerm z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open SpineApplicationTargets (parameters selectedData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem activeProgram (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) :
    BottomRepresentative.active (parameters data window) window = SpineRepresentative.active data window := rfl

theorem outerProgram (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) :
    BottomRepresentative.representative (parameters data window) window =
      InternalAcceptance.branch (SpineRepresentative.active data window)
        (SpineRepresentative.representative data window)
        (InternalAcceptance.branch
          (BottomRepresentative.sameBottom (SpineRepresentative.representative data window))
          (.projection 0) (SpineRepresentative.representative data window)) := rfl

theorem markIffRename {β : Type} (mark out input : OTerm α) (j : α → β) :
    ((BottomSpineMeasure.graph mark out).iff (BottomSpineMeasure.graph mark input)).relabel j =
      (BottomSpineMeasure.graph (mark.relabel j) (out.relabel j)).iff
        (BottomSpineMeasure.graph (mark.relabel j) (input.relabel j)) :=
  SpineRepresentativeInternalProof.markIffRename mark out input j

theorem identityObserver (mark input : OTerm α) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark input).iff (BottomSpineMeasure.graph mark input))) := by
  have h : Derivation body Gamma ((BottomSpineMeasure.graph mark input).imp
      (BottomSpineMeasure.graph mark input)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.conjunctionIntroduction h h⟩

theorem replaceOutput (mark out candidate input : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out candidate)))
    (hi : Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark candidate).iff (BottomSpineMeasure.graph mark input)))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark out).iff (BottomSpineMeasure.graph mark input))) := by
  let P := BottomSpineMeasure.graph mark out
  obtain ⟨he'⟩ := withHyp he P
  obtain ⟨hc⟩ := headTransport BottomSpineMeasure.measure mark out candidate Fin.elim0 ⟨he'⟩
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hi'⟩ := withHyp hi P
  have hf := Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionLeft hi') hc)
  let Q := BottomSpineMeasure.graph mark input
  obtain ⟨hi''⟩ := withHyp hi Q
  have hcandidate : Nonempty (Derivation body (Q :: Gamma) (BottomSpineMeasure.graph mark candidate)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi'')
      (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨he''⟩ := withHyp he Q
  obtain ⟨hb⟩ := headTransport BottomSpineMeasure.measure mark candidate out Fin.elim0 ⟨symm he''⟩ hcandidate
  exact ⟨Derivation.conjunctionIntroduction hf (Derivation.implicationIntroduction hb)⟩

def queries (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) : Fin 2 → Program 2 :=
  Fin.cons (SpineRepresentative.representative data window)
    (Fin.cons (BottomRepresentative.sameBottom (SpineRepresentative.representative data window)) Fin.elim0)

theorem query0 (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) :
    queries data window (0 : Fin 2) = SpineRepresentative.representative data window := rfl

theorem query1 (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) :
    queries data window (1 : Fin 2) =
      BottomRepresentative.sameBottom (SpineRepresentative.representative data window) := rfl

/-- The outer exact-bottom wrapper returns either the input or its oldR
candidate. Both already have the SAME full mark; no bottom-shape case is
interpreted semantically. -/
theorem outerPreservation (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1)
    (out input parameter mark : OTerm α)
    (ha : Nonempty (Derivation body Gamma
      (BottomRepresentative.activeGraph (parameters data window) window input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.representative (parameters data window) window) out input parameter))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark out).iff (BottomSpineMeasure.graph mark input))) := by
  unfold BottomRepresentative.activeGraph at ha
  rw [activeProgram] at ha
  rw [outerProgram] at hr
  let R := SpineRepresentative.representative data window
  let C := BottomRepresentative.sameBottom R
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hinner := successorBranchElim (SpineRepresentative.active data window) R
    (InternalAcceptance.branch C (.projection 0) R) out z xs ha hr
  apply queryCases (queries data window) xs _
  intro β j ys Delta hj hq
  rw [markIffRename]
  simp only [xs,consTermRename,emptyRename] at hq
  have hR := hq 0
  rw [query0] at hR
  have hC := hq 1
  rw [query1] at hC
  have ha' := renameInto ha j Delta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at ha'
  have hi' := renameInto hinner j Delta hj
  rw [graph2Rename] at hi'
  let xx : Fin 2 → OTerm β := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hsame := SpineRepresentativeInternalProof.preservation data window (ys 0)
    (input.relabel j) (parameter.relabel j) (mark.relabel j) ha' hR
  apply formulaCases (eqn (ys 1) z)
  · let P := eqn (ys 1) z
    have hz := outputTransport C (ys 1) z xx
      (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hC P)
    have ho := zeroBranchElim C (.projection 0) R (out.relabel j) xx hz (withHyp hi' P)
    have he := valueUnique (.projection (0 : Fin 2)) (out.relabel j) (input.relabel j)
      xx ho (projectionValue 0 xx)
    exact replaceOutput (mark.relabel j) (out.relabel j) (input.relabel j) (input.relabel j)
      he (identityObserver (mark.relabel j) (input.relabel j))
  · let P := (eqn (ys 1) z).not
    have ho := nonzeroBranchElim C (.projection 0) R (out.relabel j) (ys 1) xx
      (withHyp hC P)
      (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hi' P)
    have he := valueUnique R (out.relabel j) (ys 0) xx ho (withHyp hR P)
    exact replaceOutput (mark.relabel j) (out.relabel j) (ys 0) (input.relabel j) he (withHyp hsame P)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationLeafProof
