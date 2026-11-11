module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open OriginalHereditaryLambda OriginalHereditaryLambdaChildStateProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight zeroGraphNotOne)
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalControlGraphSupportProof InternalControlGraphProof InternalControlGraphChoiceProof
open InternalTagArithmeticSupportProof InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem notZeroRename {beta : Type} (state : OTerm alpha) (j : alpha → beta) :
    ((eqn state z).not).relabel j = (eqn (state.relabel j) z).not := by
  change ((eqn state z).relabel j).not = _
  rw [eqnRelabel,zRelabel]

theorem liveNonzero (state source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter))) :
    Nonempty (Derivation body Delta (eqn state z).not) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  apply programCompositionCases .succ (fun _ : Fin 1 => fullPair) state xs _ hl
  intro beta j ys Theta hj hs hg
  rw [notZeroRename]
  obtain ⟨he⟩ := valueUnique .succ (state.relabel j) (suc (ys 0)) ys hs (successorValue ys)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply
    (trans (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)))⟩

/-- Branch selection uses arbitrary nonzero object-language control values,
not only ONE and not native arithmetic. -/
theorem nonzeroBranchElim {n : Nat} (control a b : Program n)
    (out c : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (hn : Nonempty (Derivation body Delta (eqn c z).not))
    (hw : Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch control a b) out xs))) :
    Nonempty (Derivation body Delta (programGraph b out xs)) := by
  apply programCompositionCases LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0))) out xs _ hw
  intro beta j ys Theta hj ht hg
  simp only [programRename]
  have hc' := renameInto hc j Theta hj
  simp only [programRename] at hc'
  obtain ⟨hn'⟩ := (show Nonempty (Derivation body Theta (eqn (c.relabel j) z).not) from by
    simpa only [notZeroRename] using renameInto hn j Theta hj)
  obtain ⟨he⟩ := valueUnique control (ys 0) (c.relabel j)
    (fun i => (xs i).relabel j) (hg 0) hc'
  have hy : Nonempty (Derivation body Theta (eqn (ys 0) z).not) :=
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hn' _)
      (trans (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)))⟩
  have hv := conditionalAtNonzero (ys 0) (ys 1) (ys 2) hy
  rw [threeTuple] at hv
  obtain ⟨heq⟩ := valueUnique LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
    (out.relabel j) (ys 2) ys ht hv
  exact outputTransport b (ys 2) (out.relabel j) (fun i => (xs i).relabel j) ⟨symm heq⟩ (hg 2)

theorem nonzeroBranchIntro {n : Nat} (control a b : Program n)
    (out c : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control c xs)))
    (hn : Nonempty (Derivation body Delta (eqn c z).not))
    (hb : Nonempty (Derivation body Delta (programGraph b out xs))) :
    Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch control a b) out xs)) := by
  apply programCases a xs _
  intro beta j Theta av hj ha
  simp only [programRename]
  have hc' := renameInto hc j Theta hj
  have hb' := renameInto hb j Theta hj
  have hn' := renameInto hn j Theta hj
  simp only [programRename,notZeroRename] at hc' hb' hn'
  exact branchValue control a b (out.relabel j) (c.relabel j) av (out.relabel j)
    (fun i => (xs i).relabel j) hc' ha hb'
    (conditionalAtNonzero (c.relabel j) av (out.relabel j) hn')

theorem stopActive (source target certificate parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (LambdaNonbottom source target certificate parameter))) :
    Nonempty (Derivation body Delta (graph4 stop z source target certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  exact successorBranchIntro (normalize OriginalLambdaGuardLeaf.sourceLambda)
    (InternalLessThan.constantOne 4) (normalize OriginalLambdaGuardLeaf.sameBottom)
    z z xs (normalizeAccept OriginalLambdaGuardLeaf.sourceLambda xs (projectLeft h))
    (normalizeReject OriginalLambdaGuardLeaf.sameBottom xs
      (zeroGraphNotOne OriginalLambdaGuardLeaf.sameBottom xs (projectRight h)))

theorem finishZero : Nonempty (Derivation body Delta (graph1 finish z z)) :=
  zeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1) (atState stop)
    z (Fin.cons z Fin.elim0) (projectionValue 0 (Fin.cons z Fin.elim0)) (constantZeroValue _)

theorem transitionZero (oldStep : Program 4) :
    Nonempty (Derivation body Delta (graph1 (transition oldStep) z z)) :=
  zeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1) _
    z (Fin.cons z Fin.elim0) (projectionValue 0 (Fin.cons z Fin.elim0)) (constantZeroValue _)

theorem finishActive (state source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (ha : Nonempty (Derivation body Delta (LambdaNonbottom source target certificate parameter))) :
    Nonempty (Derivation body Delta (graph1 finish z state)) :=
  nonzeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1) (atState stop)
    z state (Fin.cons state Fin.elim0) (projectionValue 0 (Fin.cons state Fin.elim0))
    (liveNonzero state source target certificate parameter hl)
    (atLiveValue stop z state source target certificate parameter hl
      (stopActive source target certificate parameter ha))

abbrev activeBranch (oldStep : Program 4) : Program 1 :=
  InternalAcceptance.branch (normalize (atState (advanceGuard oldStep)))
    (InternalAcceptance.constantZero 1) (atState childLive)

theorem transitionActiveRecover (oldStep : Program 4)
    (state next source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (ha : Nonempty (Derivation body Delta (LambdaNonbottom source target certificate parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 (transition oldStep) next state))) :
    Nonempty (Derivation body Delta (graph1 (activeBranch oldStep) next state)) := by
  have houter := nonzeroBranchElim (.projection 0) (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch (normalize (atState stop)) (activeBranch oldStep) (.projection 0))
    next state (Fin.cons state Fin.elim0) (projectionValue 0 (Fin.cons state Fin.elim0))
    (liveNonzero state source target certificate parameter hl) ht
  exact zeroBranchElim (normalize (atState stop)) (activeBranch oldStep) (.projection 0)
    next (Fin.cons state Fin.elim0)
    (normalizeReject (atState stop) (Fin.cons state Fin.elim0)
      (zeroGraphNotOne (atState stop) (Fin.cons state Fin.elim0)
        (atLiveValue stop z state source target certificate parameter hl
          (stopActive source target certificate parameter ha)))) houter

/-- A nonzero result of the normalized active branch proves the actual
advance guard accepted, and recovers the literal child-live graph. -/
theorem activeBranchRecover (oldStep : Program 4) (state next : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn next z).not))
    (ht : Nonempty (Derivation body Delta (graph1 (activeBranch oldStep) next state))) :
    Nonempty (Derivation body Delta
      (graph1 (atState (advanceGuard oldStep)) (suc z) state ⊓
        graph1 (atState childLive) next state)) := by
  let P := graph1 (atState (advanceGuard oldStep)) (suc z) state
  let Q := graph1 (atState childLive) next state
  obtain ⟨ht⟩ := ht
  obtain ⟨hn⟩ := hn
  have hy : Nonempty (Derivation body (P :: Delta) (P ⊓ Q)) := by
    have hp : Nonempty (Derivation body (P :: Delta) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact combine hp (successorBranchElim (normalize (atState (advanceGuard oldStep)))
      (InternalAcceptance.constantZero 1) (atState childLive) next z (Fin.cons state Fin.elim0)
      (normalizeAccept (atState (advanceGuard oldStep)) _ hp) ⟨addHyp ht _⟩)
  have hno : Nonempty (Derivation body (P.not :: Delta) (P ⊓ Q)) := by
    have hz := zeroBranchElim (normalize (atState (advanceGuard oldStep)))
      (InternalAcceptance.constantZero 1) (atState childLive) next (Fin.cons state Fin.elim0)
      (normalizeReject (atState (advanceGuard oldStep)) _
        ⟨Derivation.hypothesis List.mem_cons_self⟩) ⟨addHyp ht _⟩
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 1) next z
      (Fin.cons state Fin.elim0) hz (constantZeroValue _)
    exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp hn _) he)⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
