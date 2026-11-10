module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeStepProof
open OriginalConstructorShape
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalConstructorShapeIteration
open SourceComputabilityCompletion.OriginalConstructorShapeIterationSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalParameterizedBoundedDescentNormalizer InternalParameterizedBoundedDescentNormalizerStepProof
open InternalParameterizedBoundedDescentNormalizerStepSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem stepProgram (data : Data) (window : Program 1) :
    step data window = .composition (choose (selectedValidity data window))
      (Fin.cons (leaf data window)
        (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0))) := rfl

theorem activeFactors (data : Data) (window : Program 1) (input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (activeGraph data window input parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) (suc z) input parameter ⊓
        validGraph (selectedValidity data window) input parameter)) :=
  OriginalVariableRepresentativeStepProof.activeFactors (baseData data window)
    window input parameter h

theorem activeNext (data : Data) (window : Program 1) (out input parameter : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 (step data window) out input parameter))) :
    Nonempty (Derivation body Gamma (activeGraph data window out parameter)) :=
  OriginalVariableRepresentativeStepProof.activeNext (baseData data window)
    window out input parameter ha ht

/-- The actual choice either returns its input or the literal guarded old
representative output. Both branches preserve the same original constructor-shape mark. -/
theorem forwardStep (data : Data) (window : Program 1) (out input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph indicator input)))
    (ht : Nonempty (Derivation body Gamma (graph2 (step data window) out input parameter))) :
    Nonempty (Derivation body Gamma (markGraph indicator out)) := by
  let R := leaf data window
  let V := selectedValidity data window
  apply programCases R (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta candidate hj hr
  rw [markRename]
  have hr' : Nonempty (Derivation body Delta
      (graph2 R candidate (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hr
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hb' := renameInto hb j Delta hj
  rw [markRename] at hb'
  have ht' := renameInto ht j Delta hj
  rw [graph2Rename] at ht'
  rw [stepProgram] at ht'
  let xs : Fin 2 → OTerm β := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let ys : Fin 3 → OTerm β := Fin.cons candidate
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
  have hc := compositionRecover (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    (out.relabel j) xs ys ht'
    (fun i => Fin.cases hr' (Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i)
  let P := programGraph (guard V) (suc z) ys
  apply formulaCases P
  · have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := successorBranchElim (guard V) (.projection (1 : Fin 3)) (.projection 0)
      (out.relabel j) z ys hp (withHyp hc P)
    obtain ⟨he⟩ := valueUnique (.projection (0 : Fin 3)) (out.relabel j) candidate ys ho (projectionValue 0 ys)
    obtain ⟨hi⟩ := OriginalConstructorShapeLeafProof.outerPreservation
      data window candidate (input.relabel j) (parameter.relabel j) (indicator.relabel j)
      (withHyp ha' P) (withHyp hr' P)
    obtain ⟨hb''⟩ := withHyp hb' P
    have hcandidate : Nonempty (Derivation body (P :: Delta) (markGraph (indicator.relabel j) candidate)) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hb''⟩
    exact headTransport mark (indicator.relabel j) candidate (out.relabel j)
      Fin.elim0 ⟨symm he⟩ hcandidate
  · have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject candidateLess
      (InternalAcceptance.conjunction (candidateValid V) sameLeft) ys
      (show Nonempty (Derivation body (P.not :: Delta) P.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho := zeroBranchElim (guard V) (.projection (1 : Fin 3)) (.projection 0)
      (out.relabel j) ys hz (withHyp hc P.not)
    obtain ⟨he⟩ := valueUnique (.projection (1 : Fin 3)) (out.relabel j) (input.relabel j) ys ho (projectionValue 1 ys)
    exact headTransport mark (indicator.relabel j) (input.relabel j) (out.relabel j)
      Fin.elim0 ⟨symm he⟩ (withHyp hb' P.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeStepProof
