module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeGuardProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeLeafProof
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
open OriginalVariableRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem markIffRename {β : Type} (mark out input : OTerm α) (j : α → β) :
    ((markGraph mark out).iff (markGraph mark input)).relabel j =
      (markGraph (mark.relabel j) (out.relabel j)).iff
        (markGraph (mark.relabel j) (input.relabel j)) :=
  OriginalVariableRepresentativeGuardProof.markIffRename mark out input j

theorem identityObserver (mark input : OTerm α) :
    Nonempty (Derivation body Gamma
      ((markGraph mark input).iff (markGraph mark input))) := by
  have h : Derivation body Gamma ((markGraph mark input).imp
      (markGraph mark input)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.conjunctionIntroduction h h⟩

theorem replaceOutput (mark out candidate input : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out candidate)))
    (hi : Nonempty (Derivation body Gamma
      ((markGraph mark candidate).iff (markGraph mark input)))) :
    Nonempty (Derivation body Gamma
      ((markGraph mark out).iff (markGraph mark input))) := by
  let P := markGraph mark out
  obtain ⟨he'⟩ := withHyp he P
  obtain ⟨hc⟩ := headTransport variableMark mark out candidate Fin.elim0 ⟨he'⟩
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hi'⟩ := withHyp hi P
  have hf := Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionLeft hi') hc)
  let Q := markGraph mark input
  obtain ⟨hi''⟩ := withHyp hi Q
  have hcandidate : Nonempty (Derivation body (Q :: Gamma) (markGraph mark candidate)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi'')
      (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨he''⟩ := withHyp he Q
  obtain ⟨hb⟩ := headTransport variableMark mark candidate out Fin.elim0 ⟨symm he''⟩ hcandidate
  exact ⟨Derivation.conjunctionIntroduction hf (Derivation.implicationIntroduction hb)⟩

def queries (R C : Program 2) : Fin 2 → Program 2 :=
  Fin.cons R (Fin.cons C Fin.elim0)

theorem query0 (R C : Program 2) : queries R C (0 : Fin 2) = R := rfl
theorem query1 (R C : Program 2) : queries R C (1 : Fin 2) = C := rfl

/-- Either literal branch retains a candidate that already has the same mark.
This is only a graph lemma; each use below supplies the actual guard proof. -/
theorem atValues (R C : Program 2) (out input parameter mark candidate control : OTerm α)
    (hr : Nonempty (Derivation body Gamma (graph2 R candidate input parameter)))
    (hc : Nonempty (Derivation body Gamma (graph2 C control input parameter)))
    (hi : Nonempty (Derivation body Gamma
      (graph2 (InternalAcceptance.branch C (.projection 0) R) out input parameter)))
    (hsame : Nonempty (Derivation body Gamma
      ((markGraph mark candidate).iff (markGraph mark input)))) :
    Nonempty (Derivation body Gamma ((markGraph mark out).iff (markGraph mark input))) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply formulaCases (eqn control z)
  · let P := eqn control z
    have hz := outputTransport C control z xs
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hc P)
    have ho := zeroBranchElim C (.projection 0) R out xs hz (withHyp hi P)
    have he := valueUnique (.projection (0 : Fin 2)) out input xs ho (projectionValue 0 xs)
    exact replaceOutput mark out input input he (identityObserver mark input)
  · let P := (eqn control z).not
    have ho := nonzeroBranchElim C (.projection 0) R out control xs
      (withHyp hc P)
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hi P)
    have he := valueUnique R out candidate xs ho (withHyp hr P)
    exact replaceOutput mark out candidate input he (withHyp hsame P)

theorem spineProgram (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) :
    SpineRepresentative.representative (baseData data window) window =
      InternalAcceptance.branch (active data window) (representative data window)
        (InternalAcceptance.branch
          (SpineRepresentative.sameMeasure (representative data window))
          (.projection 0) (representative data window)) := rfl

theorem spinePreservation (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1)
    (out input parameter mark : OTerm α)
    (ha : Nonempty (Derivation body Gamma
      (graph2 (active data window) InternalOriginalStepGuard.one input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (SpineRepresentative.representative (baseData data window) window) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph mark out).iff (markGraph mark input))) := by
  rw [spineProgram] at hr
  let R := representative data window
  let C := SpineRepresentative.sameMeasure R
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hinner := successorBranchElim (active data window) R
    (InternalAcceptance.branch C (.projection 0) R) out z xs ha hr
  apply queryCases (queries R C) xs _
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
  have hsame := OriginalVariableRepresentativeGuardProof.preservation data window (ys 0)
    (input.relabel j) (parameter.relabel j) (mark.relabel j) ha' hR
  exact atValues R C (out.relabel j) (input.relabel j) (parameter.relabel j)
    (mark.relabel j) (ys 0) (ys 1) hR hC hi' hsame

theorem outerProgram (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1) :
    BottomRepresentative.representative (SpineApplicationTargets.parameters (baseData data window) window) window =
      InternalAcceptance.branch (active data window)
        (SpineRepresentative.representative (baseData data window) window)
        (InternalAcceptance.branch
          (BottomRepresentative.sameBottom (SpineRepresentative.representative (baseData data window) window))
          (.projection 0) (SpineRepresentative.representative (baseData data window) window)) := rfl

theorem outerPreservation (data : InternalOriginalUniformDescentSelection.Data) (window : Program 1)
    (out input parameter mark : OTerm α)
    (ha : Nonempty (Derivation body Gamma
      (graph2 (active data window) InternalOriginalStepGuard.one input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.representative
        (SpineApplicationTargets.parameters (baseData data window) window) window) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph mark out).iff (markGraph mark input))) := by
  rw [outerProgram] at hr
  let R := SpineRepresentative.representative (baseData data window) window
  let C := BottomRepresentative.sameBottom R
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hinner := successorBranchElim (active data window) R
    (InternalAcceptance.branch C (.projection 0) R) out z xs ha hr
  apply queryCases (queries R C) xs _
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
  have hsame := spinePreservation data window (ys 0)
    (input.relabel j) (parameter.relabel j) (mark.relabel j) ha' hR
  exact atValues R C (out.relabel j) (input.relabel j) (parameter.relabel j)
    (mark.relabel j) (ys 0) (ys 1) hR hC hi' hsame

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeLeafProof
