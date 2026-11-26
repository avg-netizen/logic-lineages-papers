module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationResultStack (liftP)
open InternalParameterizedApplicationResultStackWiringProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalBetaTotalityProof (addHyp)
open OriginalNonapplicationChecker
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nonapplicationRename {β : Type} (input : OTerm α) (j : α → β) :
    (nonapplicationRoot input).relabel j = nonapplicationRoot (input.relabel j) := by
  change ((graph1 (constructorTag (.projection 0)) positionTerm input).relabel j).not = _
  simp only [graph1Rename,positionTermEq,sucRelabel,zRelabel,nonapplicationRoot]

/-- Recover the literal tag at the selected raw value, using only actual
selector and tag graphs. The selected value is never decoded or reencoded. -/
theorem selectorTagRecover (selector : Program 1) (tag state value : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector value state)))
    (ht : Nonempty (Derivation body Gamma (graph1 (constructorTag selector) tag state))) :
    Nonempty (Derivation body Gamma (graph1 (constructorTag (.projection 0)) tag value)) := by
  apply programCases InternalUnpair.right (Fin.cons value Fin.elim0) _
  intro β j Delta inner hj hv
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hv
  have hs' := renameInto hs j Delta hj
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at hs' ht'
  let xs : Fin 1 → OTerm β := Fin.cons (state.relabel j) Fin.elim0
  let ys : Fin 1 → OTerm β := Fin.cons (value.relabel j) Fin.elim0
  have hi := unaryValue InternalUnpair.right selector inner (value.relabel j) xs hv hs'
  have hl := unaryRecover InternalUnpair.left (rightOf selector) (tag.relabel j) inner xs ht' hi
  exact unaryValue InternalUnpair.left (rightOf (.projection 0)) (tag.relabel j) inner ys hl
    (unaryValue InternalUnpair.right (.projection 0) inner (value.relabel j) ys hv (projectionValue 0 ys))

/-- The ORIGINAL structural guard contains the actual raw source tag-two
factor, regardless of the endpoint program or any other certificate fields. -/
theorem structuralSourceTag (state : OTerm α)
    (hg : Nonempty (Derivation body Gamma (graph1 structuralGuard (suc z) state))) :
    Nonempty (Derivation body Gamma (graph1 (constructorTag source) positionTerm state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have h1 := andRight (conjunctionRecover _ _ xs hg)
  have h2 := andRight (conjunctionRecover _ _ xs h1)
  have ht := andLeft (conjunctionRecover _ _ xs h2)
  exact sameRightRecover (constructorTag source) (two 1) positionTerm xs ht (twoValue xs)

/-- Discharge the generic repeat fixed-point premise from the literal guard.
The rejected transition returns the WHOLE original state, not its raw source. -/
theorem transitionFixed (endpoint : Program 6) (state rawSource parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 source rawSource state)))
    (hn : Nonempty (Derivation body Gamma (nonapplicationRoot rawSource))) :
    Nonempty (Derivation body Gamma (transitionGraph endpoint state state parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let P := graph2 (guardP endpoint) (suc z) state parameter
  have hreject : Nonempty (Derivation body Gamma P.not) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := andLeft (conjunctionRecover (liftP structuralGuard) (endpointAtP endpoint) xs hp)
    have hg := liftRecover structuralGuard (suc z) state parameter hf
    obtain ⟨hs⟩ := hs
    obtain ⟨hn⟩ := hn
    obtain ⟨ht⟩ := selectorTagRecover source positionTerm state rawSource
      ⟨addHyp hs P⟩ (structuralSourceTag state hg)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn P) ht)⟩
  have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
    (liftP structuralGuard) (endpointAtP endpoint) xs hreject
  exact zeroBranchIntro (guardP endpoint) (.projection 0) (liftP peeledState)
    state xs hz (projectionValue 0 xs)

/-- Query the ACTUAL original rawPath internally, then use the fixed-point
law for that arbitrary complete code. No parsed-list or fuel premise occurs. -/
theorem normalizerFixed (endpoint : Program 6) (state rawSource parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 source rawSource state)))
    (hn : Nonempty (Derivation body Gamma (nonapplicationRoot rawSource))) :
    Nonempty (Derivation body Gamma (normalizerGraph endpoint state state parameter)) := by
  apply programCases rawPath (Fin.cons state Fin.elim0) _
  intro β j Delta code hj hc
  rw [normalizerGraphRename]
  simp only [consTermRename,emptyRename] at hc
  have hs' := renameInto hs j Delta hj
  have hn' := renameInto hn j Delta hj
  rw [graph1Rename] at hs'
  rw [nonapplicationRename] at hn'
  let xs : Fin 2 → OTerm β := Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hf := transitionFixed endpoint (state.relabel j) (rawSource.relabel j)
    (parameter.relabel j) hs' hn'
  have hr := OriginalNonapplicationCheckerFixedProof.fixedValue (transitionP endpoint)
    code (state.relabel j) (parameter.relabel j) hf
  apply compositionValue (repeatP (transitionP endpoint))
    ![liftP rawPath,.projection 0,.projection 1] (state.relabel j) xs
    (Fin.cons code (Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) hr
  intro i
  exact Fin.cases (liftValue rawPath code (state.relabel j) (parameter.relabel j) hc)
    (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (fun k => Fin.elim0 k))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerGuardProof
