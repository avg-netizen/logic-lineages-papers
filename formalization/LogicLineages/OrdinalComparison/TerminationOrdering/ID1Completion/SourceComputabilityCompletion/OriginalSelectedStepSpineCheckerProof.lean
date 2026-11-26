module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineNormalizerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineCheckerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (binaryRecover)
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationStepCheckerGraphProof (edgeStateValue)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open OriginalSpineGuardLeaf OriginalSelectedStepSpineStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem atState (endpoint : Program 6) (leaf : Program 4) (hLeaf : LeafHasSpineGuard leaf)
    (state s t k parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint leaf (suc z) s t k parameter))) :
    Nonempty (Derivation body Gamma (spineAccepted s t k parameter)) := by
  apply programCases (normalizerP endpoint) (Fin.cons state (Fin.cons parameter Fin.elim0)) _
  intro beta j Delta normalized hj hn
  rw [spineAcceptedRename]
  simp only [consTermRename,emptyRename] at hn
  have he' := renameInto he j Delta hj
  rw [graph3Rename] at he'
  have hc' := renameInto hc j Delta hj
  simp only [checkerGraphRename,sucRelabel,zRelabel] at hc'
  let xs : Fin 4 → OTerm beta := Fin.cons (s.relabel j)
    (Fin.cons (t.relabel j) (Fin.cons (k.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
  let ps : Fin 2 → OTerm beta :=
    Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hs := binaryRecover (checkedStateP endpoint leaf) edgeStateP (.projection 3)
    (suc z) (state.relabel j) (parameter.relabel j) xs hc'
    (edgeStateValue (state.relabel j) (s.relabel j) (t.relabel j) (k.relabel j)
      (parameter.relabel j) he') (projectionValue 3 xs)
  have hl := binaryRecover (selectedCheckerP leaf) (normalizerP endpoint) (.projection 1)
    (suc z) normalized (parameter.relabel j) ps hs hn (projectionValue 1 ps)
  have hg := leafStateValue leaf hLeaf normalized (parameter.relabel j) hl
  exact stateRecover (state.relabel j) (s.relabel j) (t.relabel j) (k.relabel j)
    (parameter.relabel j) he'
    (OriginalSelectedStepSpineNormalizerProof.normalizerBackward endpoint
      (state.relabel j) normalized (parameter.relabel j) hn hg)

/-- Bind the actual raw edge state, normalize along its literal certificate
path, use the leaf supplier there, and reverse the SAME original transitions. -/
theorem checkerValue (endpoint : Program 6) (leaf : Program 4) (hLeaf : LeafHasSpineGuard leaf)
    (s t k parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint leaf (suc z) s t k parameter))) :
    Nonempty (Derivation body Gamma (spineAccepted s t k parameter)) := by
  apply programCases edgeCode (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) _
  intro beta j Delta state hj he
  rw [spineAcceptedRename]
  simp only [consTermRename,emptyRename] at he
  have hc' := renameInto hc j Delta hj
  simp only [checkerGraphRename,sucRelabel,zRelabel] at hc'
  exact atState endpoint leaf hLeaf state (s.relabel j) (t.relabel j) (k.relabel j)
    (parameter.relabel j) he hc'

theorem actualOriginalSelectedStepSpineTransport :
    OriginalSelectedStepSpineTargets.ActualOriginalSelectedStepSpineTransport := by
  intro endpoint leaf hLeaf body alpha Delta s t k parameter
  let P := checkerGraph endpoint leaf InternalOriginalStepGuard.one s t k parameter
  obtain ⟨h⟩ := checkerValue (body := body) (Gamma := P :: Delta)
    endpoint leaf hLeaf s t k parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineCheckerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineCheckerProof
