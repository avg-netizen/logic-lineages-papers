module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalOriginalUniformDescentSelection (Data validity)
open InternalBetaTotalityProof (addHyp)
open UniformCertificateCompletion OriginalNonapplicationChecker
open OriginalNonapplicationCheckerGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem variableNonapplication (input : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest (suc z) input))) :
    Nonempty (Derivation body Gamma (nonapplicationRoot input)) := by
  let tag : Program 1 := InternalApplicationStepPeel.constructorTag (.projection 0)
  let xs : Fin 1 → OTerm α := Fin.cons input Fin.elim0
  let P := graph1 tag positionTerm input
  have hz := sameRightRecover tag (InternalAcceptance.constantZero 1) z xs hv (constantZeroValue xs)
  obtain ⟨hz⟩ := hz
  obtain ⟨he⟩ := valueUnique tag positionTerm z xs
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp hz P⟩
  rw [positionTermEq] at he
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

/-- Exact bottomTest supplies both original type occurrences. Its unknown
outer type is bound internally before using paid bottom graph reconstruction. -/
theorem bottomNonapplication (input : OTerm α)
    (hb : Nonempty (Derivation body Gamma
      (graph1 BottomRepresentative.bottomTest (suc z) input))) :
    Nonempty (Derivation body Gamma (nonapplicationRoot input)) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro β j Delta typ hj hl
  rw [nonapplicationRename]
  simp only [consTermRename,emptyRename] at hl
  have hb' := renameInto hb j Delta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hb'
  have hc := BottomSourceShapeProof.bottomRecover (input.relabel j) typ hl hb'
  have ht := BottomSourceValidityProof.bottomConstructorTag (input.relabel j) typ hc
  let tag : Program 1 := InternalApplicationStepPeel.constructorTag (.projection 0)
  let xs : Fin 1 → OTerm β := Fin.cons (input.relabel j) Fin.elim0
  let P := graph1 tag positionTerm (input.relabel j)
  obtain ⟨ht⟩ := ht
  obtain ⟨he⟩ := valueUnique tag positionTerm (numeral 3) xs
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp ht P⟩
  rw [positionTermEq] at he
  change Derivation body (P :: Delta) (eqn (suc (suc z)) (suc (suc (suc z)))) at he
  exact ⟨Derivation.implicationIntroduction (zeroNeSuc (cancelSuc (cancelSuc he)))⟩

/-- Recover only the literal selected-checker factor. Every actual source,
packed-target and target source-validity guard remains in the original AST. -/
theorem selectedAcceptance (data : Data) (oldStep : Program 4)
    (s t k parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (OriginalConstructorLeaf.accepted (stepChecker data oldStep) s t k parameter))) :
    Nonempty (Derivation body Gamma
      (OriginalConstructorLeaf.accepted
        (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) s t k parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  have hb := andLeft (conjunctionRecover
    (InternalAcceptance.conjunction (rawGuards data)
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep))
    (validityAt (validity data) 1) xs h)
  exact andRight (conjunctionRecover (rawGuards data)
    (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) xs hb)

theorem normalizedCases (data : Data) (oldStep : Program 4) :
    OriginalConstructorLeaf.ConstructorCases (stepChecker data (OriginalConstructorLeaf.refined oldStep)) := by
  intro body α Delta s t k parameter typeCode
  let leaf := OriginalConstructorLeaf.refined oldStep
  let step := stepChecker data leaf
  constructor
  · let P := OriginalConstructorLeaf.accepted step s t k parameter ⊓
      (graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one s ⊓
        graph1 InternalUnpair.left typeCode s)
    have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := andLeft (andRight hp)
    have hs := selectedAcceptance data leaf s t k parameter (andLeft hp)
    have hold := OriginalNonapplicationCheckerCollapseProof.checkerForward
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) leaf
      (suc z) s t k parameter (variableNonapplication s hv) hs
    obtain ⟨h⟩ := OriginalConstructorLeafInternalProof.variableBottom oldStep s t k parameter typeCode
      hold hv (andRight (andRight hp))
    exact ⟨Derivation.implicationIntroduction h⟩
  · let B := graph1 BottomRepresentative.bottomTest InternalOriginalStepGuard.one s
    let P := OriginalConstructorLeaf.accepted step s t k parameter
    have hb : Nonempty (Derivation body (P :: B :: Delta) B) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hp : Nonempty (Derivation body (P :: B :: Delta) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hs := selectedAcceptance data leaf s t k parameter hp
    obtain ⟨hold⟩ := OriginalNonapplicationCheckerCollapseProof.checkerForward
      (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) leaf
      (suc z) s t k parameter (bottomNonapplication s hb) hs
    obtain ⟨hn⟩ := OriginalConstructorLeafInternalProof.bottomReject oldStep s t k parameter hb
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationIntroduction (Derivation.implicationElimination hn hold))⟩

/-- The final representative refinement preserves the already once-refined
oldStep literally; no new global witness or additional step guard is chosen. -/
theorem refinedOldStep (p : GlobalSourcePackage.Inputs) :
    (OriginalVariableRepresentative.refineInputs p).oldStep = OriginalConstructorLeaf.refined p.oldStep := rfl

theorem actualOriginalNormalizedConstructorCases :
    OriginalNonapplicationCheckerTargets.ActualOriginalNormalizedConstructorCases := by
  intro p
  change OriginalConstructorLeaf.ConstructorCases
    (stepChecker
      (OuterSelection.data (OriginalVariableRepresentative.refineInputs p).base
        (OriginalVariableRepresentative.refineInputs p).window)
      (OriginalVariableRepresentative.refineInputs p).oldStep)
  rw [refinedOldStep]
  exact normalizedCases _ p.oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerConstructorProof
