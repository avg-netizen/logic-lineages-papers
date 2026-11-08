module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerPeelWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalParameterizedApplicationStepCheckerPeelWitnessProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalParameterizedApplicationResultStack (liftP)
open InternalParameterizedApplicationResultStackWiringProof
open InternalParameterizedApplicationStepCheckerRepeatProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem edgeStateValue (state s t k parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k))) :
    Nonempty (Derivation body Gamma (graph4 edgeStateP state s t k parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  apply compositionValue edgeCode ![.projection 0,.projection 1,.projection 2]
    state xs (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) he
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (fun j => Fin.elim0 j))) i

/-- A common original normalizer output supplies full-output equivalence.
The arbitrary old checker receives the same unchanged parameter. -/
theorem checkerTransferAtValue (endpoint : Program 6) (oldChecker : Program 4)
    (s t k s' t' k' state state' normalized out parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (he' : Nonempty (Derivation body Gamma (graph3 edgeCode state' s' t' k')))
    (hn : Nonempty (Derivation body Gamma (normalizerGraph endpoint normalized state parameter)))
    (hn' : Nonempty (Derivation body Gamma (normalizerGraph endpoint normalized state' parameter)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s' t' k' parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  let xs' : Fin 4 → OTerm α := Fin.cons s' (Fin.cons t' (Fin.cons k' (Fin.cons parameter Fin.elim0)))
  let sp : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let sp' : Fin 2 → OTerm α := Fin.cons state' (Fin.cons parameter Fin.elim0)
  have hs := binaryRecover (checkedStateP endpoint oldChecker) edgeStateP (.projection 3)
    out state parameter xs hc (edgeStateValue state s t k parameter he) (projectionValue 3 xs)
  have hv := binaryRecover (selectedCheckerP oldChecker) (normalizerP endpoint) (.projection 1)
    out normalized parameter sp hs hn (projectionValue 1 sp)
  have hs' := binaryValue (selectedCheckerP oldChecker) (normalizerP endpoint) (.projection 1)
    out normalized parameter sp' hv hn' (projectionValue 1 sp')
  exact binaryValue (checkedStateP endpoint oldChecker) edgeStateP (.projection 3)
    out state' parameter xs' hs' (edgeStateValue state' s' t' k' parameter he') (projectionValue 3 xs')

/-- The original lifted transition occurs before the raw tail repetitions.
Both initial states are unmodified original edgeCode values. -/
theorem liftedNormalizerAtValues (endpoint : Program 6)
    (d e arrow s t a k s' t' k' state state' path prefixed payload normalized parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k' parameter)))
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (he' : Nonempty (Derivation body Gamma (graph3 edgeCode state' s' t' k')))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left path k)))
    (hl' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left prefixed k')))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload k)))
    (hn : Nonempty (Derivation body Gamma (normalizerGraph endpoint normalized state parameter))) :
    Nonempty (Derivation body Gamma (normalizerGraph endpoint normalized state' parameter)) := by
  have hs := edgeSelectors state s t k he
  have hs' := edgeSelectors state' s' t' k' he'
  have hpath := unaryValue InternalUnpair.left step path k (Fin.cons state Fin.elim0)
    hl (andRight (andRight hs))
  have hprefix := unaryValue InternalUnpair.left step prefixed k' (Fin.cons state' Fin.elim0)
    hl' (andRight (andRight hs'))
  have hrest := andRight (andRight (andRight (andRight hp)))
  have happ := andRight hrest
  have htag : Nonempty (Derivation body Gamma (taggedEdge d e arrow s t a state k)) :=
    andIntro (andLeft hp) (andIntro (andLeft (andRight hp))
      (andIntro (andLeft (andRight (andRight hp)))
        (andIntro (andLeft (andRight (andRight (andRight hp)))) he)))
  have hlift := edgeLiftBackward d e a state s t k s' t' k' state'
    (andIntro he happ) he'
  have htransition := liftedValue endpoint d e arrow s t a state k state' parameter
    htag (andLeft hrest) hlift
  have hcons := andLeft (stepDestruction k path payload k' prefixed
    (reconstructPair k path payload hl hr) (andRight (andRight happ)) hl')
  let sp : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let sp' : Fin 2 → OTerm α := Fin.cons state' (Fin.cons parameter Fin.elim0)
  have hrepeat : Nonempty (Derivation body Gamma
      (repeatGraph (transitionP endpoint) normalized path state parameter)) := by
    apply compositionRecover (repeatP (transitionP endpoint))
      ![liftP rawPath,.projection 0,.projection 1] normalized sp
      (Fin.cons path (Fin.cons state (Fin.cons parameter Fin.elim0))) hn
    intro i
    exact Fin.cases (liftValue rawPath path state parameter hpath)
      (Fin.cases (projectionValue 0 sp) (Fin.cases (projectionValue 1 sp)
        (fun j => Fin.elim0 j))) i
  have hrepeat' := frontConsBackward (transitionP endpoint) prefixed positionTerm path normalized
    state' state parameter hcons htransition hrepeat
  apply compositionValue (repeatP (transitionP endpoint))
    ![liftP rawPath,.projection 0,.projection 1] normalized sp'
    (Fin.cons prefixed (Fin.cons state' (Fin.cons parameter Fin.elim0))) hrepeat'
  intro i
  exact Fin.cases (liftValue rawPath prefixed state' parameter hprefix)
    (Fin.cases (projectionValue 0 sp') (Fin.cases (projectionValue 1 sp')
      (fun j => Fin.elim0 j))) i

/-- Total queries use [source,target,step,lifted source,lifted target,lifted
step,parameter]. Only the normalizer query reads the last coordinate. -/
def originalEdgeQuery : Program 7 := .composition edgeCode ![.projection 0,.projection 1,.projection 2]
def liftedEdgeQuery : Program 7 := .composition edgeCode ![.projection 3,.projection 4,.projection 5]
def originalPathQuery : Program 7 := leftOf (.projection 2)
def liftedPathQuery : Program 7 := leftOf (.projection 5)
def originalPayloadQuery : Program 7 := rightOf (.projection 2)
def normalizedQuery (endpoint : Program 6) : Program 7 :=
  .composition (normalizerP endpoint) ![originalEdgeQuery,.projection 6]
def checkerQueries (endpoint : Program 6) : Fin 6 → Program 7 :=
  ![originalEdgeQuery,liftedEdgeQuery,originalPathQuery,liftedPathQuery,
    originalPayloadQuery,normalizedQuery endpoint]

theorem checkerFromQueries (endpoint : Program 6) (oldChecker : Program 4)
    (d e arrow s t a k s' t' k' out parameter : OTerm α) (ys : Fin 6 → OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k' parameter)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (checkerQueries endpoint i) (ys i)
      (Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s' (Fin.cons t'
        (Fin.cons k' (Fin.cons parameter Fin.elim0)))))))))) :
    (Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s' t' k' parameter)) →
      Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter))) ∧
    (Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter)) →
      Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s' t' k' parameter))) := by
  let xs : Fin 7 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s'
    (Fin.cons t' (Fin.cons k' (Fin.cons parameter Fin.elim0))))))
  have he : Nonempty (Derivation body Gamma (graph3 edgeCode (ys 0) s t k)) := by
    apply compositionRecover edgeCode ![.projection 0,.projection 1,.projection 2]
      (ys 0) xs (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) (hq 0)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) i
  have he' : Nonempty (Derivation body Gamma (graph3 edgeCode (ys 1) s' t' k')) := by
    apply compositionRecover edgeCode ![.projection 3,.projection 4,.projection 5]
      (ys 1) xs (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0))) (hq 1)
    intro i
    exact Fin.cases (projectionValue 3 xs) (Fin.cases (projectionValue 4 xs)
      (Fin.cases (projectionValue 5 xs) (fun q => Fin.elim0 q))) i
  have hl := unaryRecover InternalUnpair.left (.projection 2) (ys 2) k xs (hq 2) (projectionValue 2 xs)
  have hl' := unaryRecover InternalUnpair.left (.projection 5) (ys 3) k' xs (hq 3) (projectionValue 5 xs)
  have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 4) k xs (hq 4) (projectionValue 2 xs)
  have hn := binaryRecover (normalizerP endpoint) originalEdgeQuery (.projection 6)
    (ys 5) (ys 0) parameter xs (hq 5) (hq 0) (projectionValue 6 xs)
  have hn' := liftedNormalizerAtValues endpoint d e arrow s t a k s' t' k'
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) parameter hp he he' hl hl' hr hn
  exact ⟨checkerTransferAtValue endpoint oldChecker s' t' k' s t k
      (ys 1) (ys 0) (ys 5) out parameter he' he hn' hn,
    checkerTransferAtValue endpoint oldChecker s t k s' t' k'
      (ys 0) (ys 1) (ys 5) out parameter he he' hn hn'⟩

theorem checkerForward (endpoint : Program 6) (oldChecker : Program 4)
    (d e arrow s t a k s' t' k' out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k' parameter)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s' t' k' parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter)) := by
  apply queryCases (checkerQueries endpoint)
    (Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s'
      (Fin.cons t' (Fin.cons k' (Fin.cons parameter Fin.elim0))))))) _
  intro β j ys Delta hj hq
  rw [checkerGraphRename]
  have hp' := renameInto hp j Delta hj
  rw [liftedCheckerPremisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  rw [checkerGraphRename] at hc'
  simp only [consTermRename,emptyRename] at hq
  exact (checkerFromQueries endpoint oldChecker (d.relabel j) (e.relabel j) (arrow.relabel j)
    (s.relabel j) (t.relabel j) (a.relabel j) (k.relabel j)
    (s'.relabel j) (t'.relabel j) (k'.relabel j) (out.relabel j) (parameter.relabel j) ys hp' hq).1 hc'

theorem checkerBackward (endpoint : Program 6) (oldChecker : Program 4)
    (d e arrow s t a k s' t' k' out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k' parameter)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s' t' k' parameter)) := by
  apply queryCases (checkerQueries endpoint)
    (Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s'
      (Fin.cons t' (Fin.cons k' (Fin.cons parameter Fin.elim0))))))) _
  intro β j ys Delta hj hq
  rw [checkerGraphRename]
  have hp' := renameInto hp j Delta hj
  rw [liftedCheckerPremisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  rw [checkerGraphRename] at hc'
  simp only [consTermRename,emptyRename] at hq
  exact (checkerFromQueries endpoint oldChecker (d.relabel j) (e.relabel j) (arrow.relabel j)
    (s.relabel j) (t.relabel j) (a.relabel j) (k.relabel j)
    (s'.relabel j) (t'.relabel j) (k'.relabel j) (out.relabel j) (parameter.relabel j) ys hp' hq).2 hc'

theorem actualParameterizedOriginalLiftedChecker :
    InternalParameterizedApplicationStepCheckerTargets.ActualParameterizedOriginalLiftedChecker := by
  intro body endpoint oldChecker α Delta d e arrow s t a k s' t' k' out parameter
  apply guardedIffAt
  · exact checkerForward endpoint oldChecker d e arrow s t a k s' t' k' out parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerBackward endpoint oldChecker d e arrow s t a k s' t' k' out parameter
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerGraphProof
