module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationResultStackWiringProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof OriginalSpineGuardLeaf UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The literal four-input guard wired to the three ORIGINAL edge selectors
and the SAME separately carried parameter. -/
def stateTest : Program 2 :=
  selectedCheckerP (PositiveGuard.spineGuard BottomSpineMeasure.measure)

abbrev stateGuard (state parameter : OTerm alpha) : Formula alpha :=
  graph2 stateTest (suc z) state parameter

theorem stateGuardRename {beta : Type} (state parameter : OTerm alpha) (j : alpha → beta) :
    (stateGuard state parameter).relabel j = stateGuard (state.relabel j) (parameter.relabel j) := by
  simp only [stateGuard,graph2Rename,sucRelabel,zRelabel]

theorem spineAcceptedRename {beta : Type} (s t k parameter : OTerm alpha) (j : alpha → beta) :
    (spineAccepted s t k parameter).relabel j =
      spineAccepted (s.relabel j) (t.relabel j) (k.relabel j) (parameter.relabel j) := by
  simp only [spineAccepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem selectedRecover (leaf : Program 4) (state s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hg : Nonempty (Derivation body Gamma (graph2 (selectedCheckerP leaf) (suc z) state parameter))) :
    Nonempty (Derivation body Gamma (graph4 leaf (suc z) s t k parameter)) := by
  have hs := edgeSelectors state s t k he
  have h := wireRecover leaf ![source,target,step] (suc z) state parameter
    (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hg
    (fun i => Fin.cases (andLeft hs) (Fin.cases (andLeft (andRight hs))
      (Fin.cases (andRight (andRight hs)) (fun q => Fin.elim0 q))) i)
  rw [appendParameterThree] at h
  exact h

theorem selectedValue (leaf : Program 4) (state s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hg : Nonempty (Derivation body Gamma (graph4 leaf (suc z) s t k parameter))) :
    Nonempty (Derivation body Gamma (graph2 (selectedCheckerP leaf) (suc z) state parameter)) := by
  have hs := edgeSelectors state s t k he
  apply wireValue leaf ![source,target,step] (suc z) state parameter
    (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0)))
  · simpa only [appendParameterThree] using hg
  · intro i
    exact Fin.cases (andLeft hs) (Fin.cases (andLeft (andRight hs))
      (Fin.cases (andRight (andRight hs)) (fun q => Fin.elim0 q))) i

theorem stateRecover (state s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hg : Nonempty (Derivation body Gamma (stateGuard state parameter))) :
    Nonempty (Derivation body Gamma (spineAccepted s t k parameter)) :=
  selectedRecover (PositiveGuard.spineGuard BottomSpineMeasure.measure) state s t k parameter he hg

theorem stateValue (state s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hg : Nonempty (Derivation body Gamma (spineAccepted s t k parameter))) :
    Nonempty (Derivation body Gamma (stateGuard state parameter)) :=
  selectedValue (PositiveGuard.spineGuard BottomSpineMeasure.measure) state s t k parameter he hg

/-- The leaf supplier is applied only after all actual selector values are
bound by totality. No decoded or well-formed state is supplied by the caller. -/
theorem leafStateValue (leaf : Program 4) (hLeaf : LeafHasSpineGuard leaf)
    (state parameter : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma (graph2 (selectedCheckerP leaf) (suc z) state parameter))) :
    Nonempty (Derivation body Gamma (stateGuard state parameter)) := by
  apply queryCases (![source,target,step] : Fin 3 → Program 1) (Fin.cons state Fin.elim0) _
  intro beta j ys Delta hj hq
  rw [stateGuardRename]
  simp only [consTermRename,emptyRename] at hq
  have he := edgeReconstruction (state.relabel j) (ys 0) (ys 1) (ys 2)
    (andIntro (hq 0) (andIntro (hq 1) (hq 2)))
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  obtain ⟨ha⟩ := selectedRecover leaf (state.relabel j) (ys 0) (ys 1) (ys 2)
    (parameter.relabel j) he hg'
  obtain ⟨h⟩ := hLeaf body beta Delta (ys 0) (ys 1) (ys 2) (parameter.relabel j)
  exact stateValue (state.relabel j) (ys 0) (ys 1) (ys 2) (parameter.relabel j) he
    ⟨Derivation.implicationElimination h ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineStateProof
