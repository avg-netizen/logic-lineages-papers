module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalParameterizedBoundedDescentNormalizer
open InternalParameterizedBoundedDescentNormalizerStepSupportProof
open InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Uniform derivation supplier, without any correctness field in a Program tuple. -/
def OldPreservation (condition R : Program 2) (observer : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (out input parameter mark : OTerm α),
    Nonempty (Derivation body Gamma (graph2 condition InternalOriginalStepGuard.one input parameter)) →
    Nonempty (Derivation body Gamma (graph2 R out input parameter)) →
    Nonempty (Derivation body Gamma ((graph2 observer mark out parameter).iff (graph2 observer mark input parameter)))

theorem observerIffRename {β : Type} (observer : Program 2)
    (mark out input parameter : OTerm α) (j : α → β) :
    ((graph2 observer mark out parameter).iff (graph2 observer mark input parameter)).relabel j =
      (graph2 observer (mark.relabel j) (out.relabel j) (parameter.relabel j)).iff
        (graph2 observer (mark.relabel j) (input.relabel j) (parameter.relabel j)) := by
  change ((graph2 observer mark out parameter).relabel j).iff
    ((graph2 observer mark input parameter).relabel j) = _
  rw [graph2Rename, graph2Rename]

theorem identityObserver (observer : Program 2) (mark input parameter : OTerm α) :
    Nonempty (Derivation body Gamma
      ((graph2 observer mark input parameter).iff (graph2 observer mark input parameter))) := by
  have h : Derivation body Gamma ((graph2 observer mark input parameter).imp
      (graph2 observer mark input parameter)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.conjunctionIntroduction h h⟩

theorem replaceOutput (observer : Program 2) (mark out candidate input parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out candidate)))
    (hi : Nonempty (Derivation body Gamma
      ((graph2 observer mark candidate parameter).iff (graph2 observer mark input parameter)))) :
    Nonempty (Derivation body Gamma
      ((graph2 observer mark out parameter).iff (graph2 observer mark input parameter))) := by
  let P := graph2 observer mark out parameter
  obtain ⟨he'⟩ := withHyp he P
  obtain ⟨hc⟩ := headTransport observer mark out candidate (Fin.cons parameter Fin.elim0) ⟨he'⟩
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hi'⟩ := withHyp hi P
  have hf := Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionLeft hi') hc)
  let Q := graph2 observer mark input parameter
  obtain ⟨hi''⟩ := withHyp hi Q
  have hcandidate : Nonempty (Derivation body (Q :: Gamma) (graph2 observer mark candidate parameter)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi'')
      (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨he''⟩ := withHyp he Q
  obtain ⟨hb⟩ := headTransport observer mark candidate out (Fin.cons parameter Fin.elim0) ⟨symm he''⟩ hcandidate
  exact ⟨Derivation.conjunctionIntroduction hf (Derivation.implicationIntroduction hb)⟩

theorem projectionPreservation (condition : Program 2) (observer : Program 2) :
    OldPreservation condition (.projection 0) observer := by
  intro body α Gamma out input parameter mark _ hr
  have he := valueUnique (.projection (0 : Fin 2)) out input ![input,parameter] hr
    (projectionValue 0 ![input,parameter])
  exact replaceOutput observer mark out input input parameter he (identityObserver observer mark input parameter)

/-- Both genuine branches independently preserve the same observer. -/
theorem branchPreservation (condition C R S : Program 2) (observer : Program 2)
    (hR : OldPreservation condition R observer) (hS : OldPreservation condition S observer) :
    OldPreservation condition (InternalAcceptance.branch C R S) observer := by
  intro body α Gamma out input parameter mark ha hr
  apply programCases C (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta control hj hc
  rw [observerIffRename]
  have hc' : Nonempty (Derivation body Delta
      (graph2 C control (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hc
  have ha' := renameInto ha j Delta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at ha'
  have hr' := renameInto hr j Delta hj
  rw [graph2Rename] at hr'
  let xs : Fin 2 → OTerm β := ![input.relabel j,parameter.relabel j]
  apply formulaCases (eqn control z)
  · let P := eqn control z
    have hz := outputTransport C control z xs
      (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hc' P)
    have ho := zeroBranchElim C R S (out.relabel j) xs hz (withHyp hr' P)
    exact hR body β (P :: Delta) (out.relabel j) (input.relabel j)
      (parameter.relabel j) (mark.relabel j) (withHyp ha' P) ho
  · let P := (eqn control z).not
    have ho := nonzeroBranchElim C R S (out.relabel j) control xs (withHyp hc' P)
      (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp hr' P)
    exact hS body β (P :: Delta) (out.relabel j) (input.relabel j)
      (parameter.relabel j) (mark.relabel j) (withHyp ha' P) ho

/-- Every literal observer guard returns the previous output or the whole input. -/
theorem observedPreservation (condition active : Program 2) (mark : Program 1)
    (previous : Program 2) (observer : Program 2)
    (hPrevious : OldPreservation condition previous observer) :
    OldPreservation condition
      (OriginalApplicationSidecarTransitionPipelineDefinitions.observed active mark previous) observer :=
  branchPreservation condition active previous _ observer hPrevious
    (branchPreservation condition _ (.projection 0) previous observer
      (projectionPreservation condition observer) hPrevious)

/-- Accepted descent returns the actual old candidate; rejection returns the input. -/
theorem transitionPreservation (condition R V : Program 2) (observer : Program 2)
    (hR : OldPreservation condition R observer) :
    OldPreservation condition (transition R V) observer := by
  intro body α Gamma out input parameter mark ha ht
  apply programCases R (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta candidate hj hr
  rw [observerIffRename]
  have hr' : Nonempty (Derivation body Delta
      (graph2 R candidate (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hr
  have ha' := renameInto ha j Delta hj
  simp only [graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at ha'
  have ht' := renameInto ht j Delta hj
  rw [graph2Rename] at ht'
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
    have he := valueUnique (.projection (0 : Fin 3)) (out.relabel j) candidate ys ho (projectionValue 0 ys)
    exact replaceOutput observer (mark.relabel j) (out.relabel j) candidate (input.relabel j) (parameter.relabel j) he
      (hR body β (P :: Delta) candidate (input.relabel j) (parameter.relabel j) (mark.relabel j)
        (withHyp ha' P) (withHyp hr' P))
  · have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject candidateLess
      (InternalAcceptance.conjunction (candidateValid V) sameLeft) ys
      (show Nonempty (Derivation body (P.not :: Delta) P.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho := zeroBranchElim (guard V) (.projection (1 : Fin 3)) (.projection 0)
      (out.relabel j) ys hz (withHyp hc P.not)
    have he := valueUnique (.projection (1 : Fin 3)) (out.relabel j) (input.relabel j) ys ho (projectionValue 1 ys)
    exact replaceOutput observer (mark.relabel j) (out.relabel j) (input.relabel j) (input.relabel j) (parameter.relabel j)
      he (identityObserver observer (mark.relabel j) (input.relabel j) (parameter.relabel j))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyWrapperProof
