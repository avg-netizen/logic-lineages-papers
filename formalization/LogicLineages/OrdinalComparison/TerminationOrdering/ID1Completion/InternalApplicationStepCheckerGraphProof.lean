module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerGraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel InternalApplicationStepChecker
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalApplicationStepPeelWitnessProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRawListRepeat InternalRawListRepeatProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem liftedCheckerPremisesRename {β : Type} (endpoint : Program 5)
    (d e arrow s t a k s' t' k' : OTerm α) (j : α → β) :
    (liftedCheckerPremises endpoint d e arrow s t a k s' t' k').relabel j =
      liftedCheckerPremises endpoint (d.relabel j) (e.relabel j) (arrow.relabel j)
        (s.relabel j) (t.relabel j) (a.relabel j) (k.relabel j)
        (s'.relabel j) (t'.relabel j) (k'.relabel j) := by
  simp only [liftedCheckerPremises,conjunctionRename,graph1Rename,graph2Rename,
    graph4Rename,graph5Rename,sucRelabel,zRelabel]

/-- A common normalizer output supplies full-output equivalence for any old
checker, without an assumption about its meaning or acceptance behavior. -/
theorem checkerTransferAtValue (endpoint : Program 5) (oldChecker : Program 3)
    (s t k s' t' k' state state' normalized out : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (he' : Nonempty (Derivation body Gamma (graph3 edgeCode state' s' t' k')))
    (hn : Nonempty (Derivation body Gamma (graph1 (normalizer endpoint) normalized state)))
    (hn' : Nonempty (Derivation body Gamma (graph1 (normalizer endpoint) normalized state')))
    (hc : Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s t k))) :
    Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s' t' k')) := by
  have hs := unaryRecover (checkedState endpoint oldChecker) edgeCode out state
    (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hc he
  have hv := unaryRecover (.composition oldChecker ![source,target,step])
    (normalizer endpoint) out normalized (Fin.cons state Fin.elim0) hs hn
  have hs' := unaryValue (.composition oldChecker ![source,target,step])
    (normalizer endpoint) out normalized (Fin.cons state' Fin.elim0) hv hn'
  exact unaryValue (checkedState endpoint oldChecker) edgeCode out state'
    (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0))) hs' he'

/-- The first original lifted transition is performed before the remaining
raw-list repetitions. Its common output is derived, never postulated. -/
theorem liftedNormalizerAtValues (endpoint : Program 5)
    (d e arrow s t a k s' t' k' state state' path prefixed payload normalized : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k')))
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (he' : Nonempty (Derivation body Gamma (graph3 edgeCode state' s' t' k')))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left path k)))
    (hl' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left prefixed k')))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload k)))
    (hn : Nonempty (Derivation body Gamma (graph1 (normalizer endpoint) normalized state))) :
    Nonempty (Derivation body Gamma (graph1 (normalizer endpoint) normalized state')) := by
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
  have htransition := liftedValue endpoint d e arrow s t a state k state'
    htag (andLeft hrest) hlift
  have hcons := andLeft (stepDestruction k path payload k' prefixed
    (reconstructPair k path payload hl hr) (andRight (andRight happ)) hl')
  have hrepeat := binaryRecover (repeatProgram (transition endpoint)) rawPath (.projection 0)
    normalized path state (Fin.cons state Fin.elim0) hn hpath
    (projectionValue 0 (Fin.cons state Fin.elim0))
  have hrepeat' := frontConsBackward (transition endpoint) prefixed positionTerm path normalized
    state' state hcons htransition hrepeat
  exact binaryValue (repeatProgram (transition endpoint)) rawPath (.projection 0)
    normalized prefixed state' (Fin.cons state' Fin.elim0) hrepeat' hprefix
    (projectionValue 0 (Fin.cons state' Fin.elim0))

/-- Queries use only original total programs on [source,target,step,lifted
source,lifted target,lifted step]. Their six witnesses are eliminated below. -/
def originalEdgeQuery : Program 6 := .composition edgeCode ![.projection 0,.projection 1,.projection 2]
def liftedEdgeQuery : Program 6 := .composition edgeCode ![.projection 3,.projection 4,.projection 5]
def originalPathQuery : Program 6 := leftOf (.projection 2)
def liftedPathQuery : Program 6 := leftOf (.projection 5)
def originalPayloadQuery : Program 6 := rightOf (.projection 2)
def normalizedQuery (endpoint : Program 5) : Program 6 :=
  .composition (normalizer endpoint) (fun _ : Fin 1 => originalEdgeQuery)
def checkerQueries (endpoint : Program 5) : Fin 6 → Program 6 :=
  ![originalEdgeQuery,liftedEdgeQuery,originalPathQuery,liftedPathQuery,
    originalPayloadQuery,normalizedQuery endpoint]

theorem checkerFromQueries (endpoint : Program 5) (oldChecker : Program 3)
    (d e arrow s t a k s' t' k' out : OTerm α) (ys : Fin 6 → OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k')))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (checkerQueries endpoint i) (ys i)
      (Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0))))))))) :
    (Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s' t' k')) →
      Nonempty (Derivation body Gamma
        (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s t k))) ∧
    (Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s t k)) →
      Nonempty (Derivation body Gamma
        (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s' t' k'))) := by
  let xs : Fin 6 → OTerm α :=
    Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0)))))
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
  have hn := unaryRecover (normalizer endpoint) originalEdgeQuery (ys 5) (ys 0) xs (hq 5) (hq 0)
  have hn' := liftedNormalizerAtValues endpoint d e arrow s t a k s' t' k'
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hp he he' hl hl' hr hn
  exact ⟨checkerTransferAtValue endpoint oldChecker s' t' k' s t k
      (ys 1) (ys 0) (ys 5) out he' he hn' hn,
    checkerTransferAtValue endpoint oldChecker s t k s' t' k'
      (ys 0) (ys 1) (ys 5) out he he' hn hn'⟩

theorem checkerForward (endpoint : Program 5) (oldChecker : Program 3)
    (d e arrow s t a k s' t' k' out : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k')))
    (hc : Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s' t' k'))) :
    Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s t k)) := by
  apply queryCases (checkerQueries endpoint)
    (Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0)))))) _
  intro β j ys Delta hj hq
  rw [graph3Rename]
  have hp' := renameInto hp j Delta hj
  rw [liftedCheckerPremisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  rw [graph3Rename] at hc'
  simp only [consTermRename,emptyRename] at hq
  exact (checkerFromQueries endpoint oldChecker (d.relabel j) (e.relabel j) (arrow.relabel j)
    (s.relabel j) (t.relabel j) (a.relabel j) (k.relabel j)
    (s'.relabel j) (t'.relabel j) (k'.relabel j) (out.relabel j) ys hp' hq).1 hc'

theorem checkerBackward (endpoint : Program 5) (oldChecker : Program 3)
    (d e arrow s t a k s' t' k' out : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k s' t' k')))
    (hc : Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s t k))) :
    Nonempty (Derivation body Gamma
      (graph3 (InternalApplicationStepPeel.checker endpoint oldChecker) out s' t' k')) := by
  apply queryCases (checkerQueries endpoint)
    (Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons s' (Fin.cons t' (Fin.cons k' Fin.elim0)))))) _
  intro β j ys Delta hj hq
  rw [graph3Rename]
  have hp' := renameInto hp j Delta hj
  rw [liftedCheckerPremisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  rw [graph3Rename] at hc'
  simp only [consTermRename,emptyRename] at hq
  exact (checkerFromQueries endpoint oldChecker (d.relabel j) (e.relabel j) (arrow.relabel j)
    (s.relabel j) (t.relabel j) (a.relabel j) (k.relabel j)
    (s'.relabel j) (t'.relabel j) (k'.relabel j) (out.relabel j) ys hp' hq).2 hc'

theorem actualOriginalLiftedChecker :
    InternalApplicationStepCheckerTargets.ActualOriginalLiftedChecker := by
  intro body endpoint oldChecker α d e arrow s t a k s' t' k' out
  apply guardedIff
  · exact checkerForward endpoint oldChecker d e arrow s t a k s' t' k' out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact checkerBackward endpoint oldChecker d e arrow s t a k s' t' k' out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerGraphProof
