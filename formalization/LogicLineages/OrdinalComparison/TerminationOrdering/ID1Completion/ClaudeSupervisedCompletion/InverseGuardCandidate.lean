module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerPeelCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedCheckerInverseGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationStepCheckerGraphProof (edgeStateValue)
open InternalParameterizedApplicationResultStack (liftP)
open InternalParameterizedApplicationResultStackWiringProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelComponentsProof (packedAtPairs)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof (rejectZeroRecover)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-! ## Formula abbreviations (pure conjunctions of ORIGINAL graphs) -/

/-- The recovered child witnesses of an ACCEPTED original guard: the original
lifted-checker premises at the unchanged raw application source/target/step,
the literal peeled child edge state, and the actual transition to it. -/
abbrev acceptedWitness (endpoint : Program 6)
    (d e arrow s t a k child state S T K parameter : OTerm α) : Formula α :=
  liftedCheckerPremises endpoint d e arrow s t a k S T K parameter ⊓
    (graph3 edgeCode child s t k ⊓ transitionGraph endpoint child state parameter)

/-- Peeled branch: accepted guard, recovered witnesses, and acceptance of the
SAME checker at the peeled function edge. -/
abbrev peeledBranch (endpoint : Program 6) (oldChecker : Program 4)
    (d e arrow s t a k child out state S T K parameter : OTerm α) : Formula α :=
  graph2 (guardP endpoint) (suc z) state parameter ⊓
    (acceptedWitness endpoint d e arrow s t a k child state S T K parameter ⊓
      checkerGraph endpoint oldChecker out s t k parameter)

/-- Unpeeled branch: zero guard, fixed original normalizer, and UNCHANGED
original leaf (oldChecker) acceptance at the original raw edge. -/
abbrev rejectedBranch (endpoint : Program 6) (oldChecker : Program 4)
    (out state S T K parameter : OTerm α) : Formula α :=
  graph2 (guardP endpoint) z state parameter ⊓
    (normalizerGraph endpoint state state parameter ⊓ graph4 oldChecker out S T K parameter)

/-! ## Accepted-guard inversion at explicit selector values -/

/-- Twenty original total selector queries on the unchanged raw edge state. -/
def guardQueries : Fin 20 → Program 1 :=
  ![functionCode, targetFunctionCode, argumentCode, peeledStep, arrowType,
    appDomain target, outerType target, argumentPayload target,
    functionPayload source, functionPayload target,
    rightOf source, appBody source, rightOf (appBody source),
    rightOf target, appBody target, rightOf (appBody target),
    rawPath, pathTail, rightOf step, peeledState]

/-- Reverse constructor work: from actual acceptance of the original guard and
the actual selector graphs, rebuild both raw application graphs (same raw
argument), the literal stepLift, the arrow/tag graphs and the endpoint graph,
plus the peeled child edge and the transition into it. -/
theorem inverseAtValues (endpoint : Program 6)
    (state S T K parameter s t a k arrow d e ap fp tp node nodeBody children
      tnode tnodeBody tchildren path tail payload child : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)))
    (hg : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) (suc z) state parameter)))
    (hs : Nonempty (Derivation body Gamma (graph1 functionCode s state)))
    (ht : Nonempty (Derivation body Gamma (graph1 targetFunctionCode t state)))
    (ha : Nonempty (Derivation body Gamma (graph1 argumentCode a state)))
    (hk : Nonempty (Derivation body Gamma (graph1 peeledStep k state)))
    (harr : Nonempty (Derivation body Gamma (graph1 arrowType arrow state)))
    (hd : Nonempty (Derivation body Gamma (graph1 (appDomain target) d state)))
    (hcod : Nonempty (Derivation body Gamma (graph1 (outerType target) e state)))
    (hap : Nonempty (Derivation body Gamma (graph1 (argumentPayload target) ap state)))
    (hfp : Nonempty (Derivation body Gamma (graph1 (functionPayload source) fp state)))
    (htp : Nonempty (Derivation body Gamma (graph1 (functionPayload target) tp state)))
    (hnode : Nonempty (Derivation body Gamma (graph1 (rightOf source) node state)))
    (hbody : Nonempty (Derivation body Gamma (graph1 (appBody source) nodeBody state)))
    (hch : Nonempty (Derivation body Gamma (graph1 (rightOf (appBody source)) children state)))
    (htnode : Nonempty (Derivation body Gamma (graph1 (rightOf target) tnode state)))
    (htbody : Nonempty (Derivation body Gamma (graph1 (appBody target) tnodeBody state)))
    (htch : Nonempty (Derivation body Gamma (graph1 (rightOf (appBody target)) tchildren state)))
    (hpath : Nonempty (Derivation body Gamma (graph1 rawPath path state)))
    (htail : Nonempty (Derivation body Gamma (graph1 pathTail tail state)))
    (hpay : Nonempty (Derivation body Gamma (graph1 (rightOf step) payload state)))
    (hchild : Nonempty (Derivation body Gamma (graph1 peeledState child state))) :
    Nonempty (Derivation body Gamma
      (acceptedWitness endpoint d e arrow s t a k child state S T K parameter)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  let ps : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  -- original edge selectors of the raw application state
  have hsel := edgeSelectors state S T K he
  have hS := andLeft hsel
  have hT := andLeft (andRight hsel)
  have hK := andRight (andRight hsel)
  -- split the accepted guard into structural and endpoint parts
  have hgc := conjunctionRecover (liftP structuralGuard) (endpointAtP endpoint) ps hg
  have hstruct := liftRecover structuralGuard (suc z) state parameter (andLeft hgc)
  have hend := andRight hgc
  have c1 := conjunctionRecover _ _ xs hstruct
  have c2 := conjunctionRecover _ _ xs (andRight c1)
  have c3 := conjunctionRecover _ _ xs (andRight c2)
  have c4 := conjunctionRecover _ _ xs (andRight c3)
  have c5 := conjunctionRecover _ _ xs (andRight c4)
  have c6 := conjunctionRecover _ _ xs (andRight c5)
  -- nonempty raw path, head = 2, tags = 2, outer type / domain / argument equalities
  have hnz := andLeft (rejectZeroRecover rawPath (InternalLessThan.constantOne 1) path xs
    hpath (andLeft c1))
  have hhead := sameRightRecover pathHead (two 1) positionTerm xs (andLeft c2) (twoValue xs)
  have hstag := sameRightRecover (constructorTag source) (two 1) positionTerm xs
    (andLeft c3) (twoValue xs)
  have httag := sameRightRecover (constructorTag target) (two 1) positionTerm xs
    (andLeft c4) (twoValue xs)
  have hecod := sameRightRecover (outerType source) (outerType target) e xs (andLeft c5) hcod
  have hdsrc := sameRightRecover (appDomain source) (appDomain target) d xs (andLeft c6) hd
  have hapsrc := sameRightRecover (argumentPayload source) (argumentPayload target) ap xs
    (andRight c6) hap
  -- raw source application: S = pair e (pair 2 (pair d (pair fp ap)))
  have sL := unaryRecover InternalUnpair.left source e S xs hecod hS
  have sR := unaryRecover InternalUnpair.right source node S xs hnode hS
  have nL := unaryRecover InternalUnpair.left (rightOf source) positionTerm node xs hstag hnode
  have nR := unaryRecover InternalUnpair.right (rightOf source) nodeBody node xs hbody hnode
  have bL := unaryRecover InternalUnpair.left (appBody source) d nodeBody xs hdsrc hbody
  have bR := unaryRecover InternalUnpair.right (appBody source) children nodeBody xs hch hbody
  have cL := unaryRecover InternalUnpair.left (rightOf (appBody source)) fp children xs hfp hch
  have cR := unaryRecover InternalUnpair.right (rightOf (appBody source)) ap children xs hapsrc hch
  have hpackS := packedAtPairs d e fp ap children nodeBody node S
    (reconstructPair children fp ap cL cR) (reconstructPair nodeBody d children bL bR)
    (reconstructPair node positionTerm nodeBody nL nR) (reconstructPair S e node sL sR)
  -- raw target application: T = pair e (pair 2 (pair d (pair tp ap))), SAME ap
  have tL := unaryRecover InternalUnpair.left target e T xs hcod hT
  have tR := unaryRecover InternalUnpair.right target tnode T xs htnode hT
  have tnL := unaryRecover InternalUnpair.left (rightOf target) positionTerm tnode xs httag htnode
  have tnR := unaryRecover InternalUnpair.right (rightOf target) tnodeBody tnode xs htbody htnode
  have tbL := unaryRecover InternalUnpair.left (appBody target) d tnodeBody xs hd htbody
  have tbR := unaryRecover InternalUnpair.right (appBody target) tchildren tnodeBody xs htch htbody
  have tcL := unaryRecover InternalUnpair.left (rightOf (appBody target)) tp tchildren xs htp htch
  have tcR := unaryRecover InternalUnpair.right (rightOf (appBody target)) ap tchildren xs hap htch
  have hpackT := packedAtPairs d e tp ap tchildren tnodeBody tnode T
    (reconstructPair tchildren tp ap tcL tcR) (reconstructPair tnodeBody d tchildren tbL tbR)
    (reconstructPair tnode positionTerm tnodeBody tnL tnR) (reconstructPair T e tnode tL tR)
  -- the original peeled function/target/argument codes and arrow
  have hs2 := binaryRecover InternalPairing.pairing arrowType (functionPayload source)
    s arrow fp xs hs harr hfp
  have ht2 := binaryRecover InternalPairing.pairing arrowType (functionPayload target)
    t arrow tp xs ht harr htp
  have ha2 := binaryRecover InternalPairing.pairing domain (argumentPayload source)
    a d ap xs ha hdsrc hapsrc
  have harrow2 := binaryRecover InternalListCodec.consCode domain codomain
    arrow d e xs harr hdsrc hecod
  -- raw path K = pair (cons 2 tail) payload and peeled step k = pair tail payload
  have hk2 := binaryRecover InternalPairing.pairing pathTail (rightOf step)
    k tail payload xs hk htail hpay
  have hhP := unaryRecover InternalListCodec.headCode rawPath positionTerm path xs hhead hpath
  have htP := unaryRecover InternalListCodec.tailCode rawPath tail path xs htail hpath
  have hcons := InternalListCodecDecompositionSupportProof.reconstructNonzero
    path positionTerm tail hnz hhP htP
  have hKL := unaryRecover InternalUnpair.left step path K xs hpath hK
  have hKR := unaryRecover InternalUnpair.right step payload K xs hpay hK
  have hlift := stepBackward k tail payload path K hk2 hcons (reconstructPair K path payload hKL hKR)
  -- both literal raw application graphs
  have happS := applicationBackward d e s a fp ap S (pairRight s arrow fp hs2)
    (pairRight a d ap ha2) hpackS
  have happT := applicationBackward d e t a tp ap T (pairRight t arrow tp ht2)
    (pairRight a d ap ha2) hpackT
  -- the original endpoint acceptance at the SAME parameter
  have hepg := wireRecover (endpointGuardP endpoint)
    ![domain,codomain,functionCode,targetFunctionCode,argumentCode] (suc z) state parameter
    (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0))))) hend
    (fun i => Fin.cases hdsrc (Fin.cases hecod (Fin.cases hs (Fin.cases ht
      (Fin.cases ha (fun j => Fin.elim0 j))))) i)
  rw [appendParameterFive] at hepg
  have hendp := andRight (conjunctionRecover endpointTypeGuardP endpoint _ hepg)
  have hprem : Nonempty (Derivation body Gamma
      (liftedCheckerPremises endpoint d e arrow s t a k S T K parameter)) :=
    andIntro harrow2 (andIntro (pairLeft s arrow fp hs2) (andIntro (pairLeft t arrow tp ht2)
      (andIntro (pairLeft a d ap ha2) (andIntro hendp (andIntro happS (andIntro happT hlift))))))
  -- the peeled child state and the actual accepted transition
  have hchildEdge : Nonempty (Derivation body Gamma (graph3 edgeCode child s t k)) :=
    compositionRecover edgeCode ![functionCode,targetFunctionCode,peeledStep] child xs
      (Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))) hchild
      (fun i => Fin.cases hs (Fin.cases ht (Fin.cases hk (fun j => Fin.elim0 j))) i)
  have htrans : Nonempty (Derivation body Gamma (transitionGraph endpoint child state parameter)) :=
    successorBranchIntro (guardP endpoint) (.projection 0) (liftP peeledState) child z ps hg
      (liftValue peeledState child state parameter hchild)
  exact andIntro hprem (andIntro hchildEdge htrans)

/-- Accepted-guard inversion in original existential-elimination form: all
witnesses come from ORIGINAL Program totality (`queryCases`), with
fresh-variable renaming and context weakening. No witness is supplied. -/
theorem acceptedGuardCases (endpoint : Program 6) (state S T K parameter : OTerm α)
    (psi : Formula α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)))
    (hg : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) (suc z) state parameter)))
    (h : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      ∀ d e arrow s t a k child : OTerm β,
      Nonempty (Derivation body Delta (acceptedWitness endpoint d e arrow s t a k child
        (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply queryCases guardQueries (Fin.cons state Fin.elim0) psi
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  have he' := renameInto he j Delta hj
  rw [graph3Rename] at he'
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  exact h β j Delta hj (ys 5) (ys 6) (ys 4) (ys 0) (ys 1) (ys 2) (ys 3) (ys 19)
    (inverseAtValues endpoint (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j)
      (parameter.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8)
      (ys 9) (ys 10) (ys 11) (ys 12) (ys 13) (ys 14) (ys 15) (ys 16) (ys 17) (ys 18) (ys 19)
      he' hg' (hq 0) (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) (hq 7) (hq 8) (hq 9)
      (hq 10) (hq 11) (hq 12) (hq 13) (hq 14) (hq 15) (hq 16) (hq 17) (hq 18) (hq 19))

/-- Accepted guard plus checker acceptance at the raw application yields the
recovered witnesses AND acceptance of the SAME checker at the peeled function
edge, via the existing `checkerForward` on the now-RECOVERED premises. -/
theorem acceptedGuardChecker (endpoint : Program 6) (oldChecker : Program 4)
    (state S T K out parameter : OTerm α) (psi : Formula α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)))
    (hg : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) (suc z) state parameter)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out S T K parameter)))
    (h : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      ∀ d e arrow s t a k child : OTerm β,
      Nonempty (Derivation body Delta (acceptedWitness endpoint d e arrow s t a k child
        (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j) (parameter.relabel j) ⊓
        checkerGraph endpoint oldChecker (out.relabel j) s t k (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply acceptedGuardCases endpoint state S T K parameter psi he hg
  intro β j Delta hj d e arrow s t a k child hw
  have hc' := renameInto hc j Delta hj
  rw [checkerGraphRename] at hc'
  exact h β j Delta hj d e arrow s t a k child (andIntro hw
    (InternalParameterizedApplicationStepCheckerGraphProof.checkerForward endpoint oldChecker
      d e arrow s t a k (S.relabel j) (T.relabel j) (K.relabel j) (out.relabel j)
      (parameter.relabel j) (andLeft hw) hc'))

/-! ## Rejected guard: generic fixed repeat, unchanged leaf -/

theorem rejectedTransition (endpoint : Program 6) (state parameter : OTerm α)
    (hz : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) z state parameter))) :
    Nonempty (Derivation body Gamma (transitionGraph endpoint state state parameter)) :=
  zeroBranchIntro (guardP endpoint) (.projection 0) (liftP peeledState) state
    (Fin.cons state (Fin.cons parameter Fin.elim0)) hz
    (projectionValue 0 (Fin.cons state (Fin.cons parameter Fin.elim0)))

/-- Any zero guard (not only a non-application root) fixes the original
normalizer along the ACTUAL raw path, queried internally. -/
theorem rejectedNormalizer (endpoint : Program 6) (state parameter : OTerm α)
    (hz : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) z state parameter))) :
    Nonempty (Derivation body Gamma (normalizerGraph endpoint state state parameter)) := by
  apply programCases rawPath (Fin.cons state Fin.elim0) _
  intro β j Delta code hj hc
  rw [normalizerGraphRename]
  simp only [consTermRename,emptyRename] at hc
  have hz' := renameInto hz j Delta hj
  simp only [graph2Rename,zRelabel] at hz'
  let xs : Fin 2 → OTerm β := Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hr := OriginalNonapplicationCheckerFixedProof.fixedValue (transitionP endpoint)
    code (state.relabel j) (parameter.relabel j)
    (rejectedTransition endpoint (state.relabel j) (parameter.relabel j) hz')
  apply compositionValue (repeatP (transitionP endpoint))
    ![liftP rawPath,.projection 0,.projection 1] (state.relabel j) xs
    (Fin.cons code (Fin.cons (state.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) hr
  intro i
  exact Fin.cases (liftValue rawPath code (state.relabel j) (parameter.relabel j) hc)
    (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (fun k => Fin.elim0 k))) i

theorem rejectedLeafForward (endpoint : Program 6) (oldChecker : Program 4)
    (out state s t k parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hz : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) z state parameter)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (graph4 oldChecker out s t k parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  let sp : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let vals : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have fields := edgeSelectors state s t k he
  have hf := rejectedNormalizer endpoint state parameter hz
  have hstate := binaryRecover (checkedStateP endpoint oldChecker) edgeStateP (.projection 3)
    out state parameter xs hc (edgeStateValue state s t k parameter he) (projectionValue 3 xs)
  have hselected := binaryRecover (selectedCheckerP oldChecker) (normalizerP endpoint) (.projection 1)
    out state parameter sp hstate hf (projectionValue 1 sp)
  have hold := wireRecover oldChecker ![source,target,step] out state parameter vals hselected
    (fun i => Fin.cases (andLeft fields) (Fin.cases (andLeft (andRight fields))
      (Fin.cases (andRight (andRight fields)) (fun j => Fin.elim0 j))) i)
  simpa only [vals,appendParameterThree] using hold

theorem rejectedLeafBackward (endpoint : Program 6) (oldChecker : Program 4)
    (out state s t k parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state s t k)))
    (hz : Nonempty (Derivation body Gamma (graph2 (guardP endpoint) z state parameter)))
    (hc : Nonempty (Derivation body Gamma (graph4 oldChecker out s t k parameter))) :
    Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out s t k parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k (Fin.cons parameter Fin.elim0)))
  let sp : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let vals : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have fields := edgeSelectors state s t k he
  have hf := rejectedNormalizer endpoint state parameter hz
  have hselected : Nonempty (Derivation body Gamma
      (graph2 (selectedCheckerP oldChecker) out state parameter)) := by
    apply wireValue oldChecker ![source,target,step] out state parameter vals
    · simpa only [vals,appendParameterThree] using hc
    · intro i
      exact Fin.cases (andLeft fields) (Fin.cases (andLeft (andRight fields))
        (Fin.cases (andRight (andRight fields)) (fun j => Fin.elim0 j))) i
  have hstate := binaryValue (selectedCheckerP oldChecker) (normalizerP endpoint) (.projection 1)
    out state parameter sp hselected hf (projectionValue 1 sp)
  exact binaryValue (checkedStateP endpoint oldChecker) edgeStateP (.projection 3)
    out state parameter xs hstate (edgeStateValue state s t k parameter he) (projectionValue 3 xs)

/-! ## Selected-checker split from an arbitrary acceptance proof -/

/-- The original selected checker, on an arbitrary acceptance derivation at
the raw edge state, is EITHER the unpeeled refined-leaf branch (zero guard,
fixed normalizer, unchanged oldChecker acceptance) OR the peeled branch with
internally bound child witnesses and peeled-checker acceptance. The case
split is excluded middle inside the original calculus. -/
theorem selectedCheckerCases (endpoint : Program 6) (oldChecker : Program 4)
    (out state S T K parameter : OTerm α) (psi : Formula α)
    (he : Nonempty (Derivation body Gamma (graph3 edgeCode state S T K)))
    (hc : Nonempty (Derivation body Gamma (checkerGraph endpoint oldChecker out S T K parameter)))
    (hzero : Nonempty (Derivation body
      (rejectedBranch endpoint oldChecker out state S T K parameter :: Gamma) psi))
    (hpeel : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      ∀ d e arrow s t a k child : OTerm β,
      Nonempty (Derivation body Delta (peeledBranch endpoint oldChecker d e arrow s t a k child
        (out.relabel j) (state.relabel j) (S.relabel j) (T.relabel j) (K.relabel j)
        (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply formulaCases (graph2 (guardP endpoint) (suc z) state parameter) psi
  · have hg : Nonempty (Derivation body
        (graph2 (guardP endpoint) (suc z) state parameter :: Gamma)
        (graph2 (guardP endpoint) (suc z) state parameter)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply acceptedGuardChecker endpoint oldChecker state S T K out parameter psi
      (withHyp he _) hg (withHyp hc _)
    intro β j Delta hj d e arrow s t a k child hw
    have hg' := renameInto hg j Delta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at hg'
    exact hpeel β j Delta (fun r hr => hj r (List.mem_cons_of_mem _ hr))
      d e arrow s t a k child (andIntro hg' hw)
  · have hn : Nonempty (Derivation body
        ((graph2 (guardP endpoint) (suc z) state parameter).not :: Gamma)
        (graph2 (guardP endpoint) (suc z) state parameter).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
      (liftP structuralGuard) (endpointAtP endpoint)
      (Fin.cons state (Fin.cons parameter Fin.elim0)) hn
    have he' := withHyp he ((graph2 (guardP endpoint) (suc z) state parameter).not)
    have hc' := withHyp hc ((graph2 (guardP endpoint) (suc z) state parameter).not)
    have hr : Nonempty (Derivation body
        ((graph2 (guardP endpoint) (suc z) state parameter).not :: Gamma)
        (rejectedBranch endpoint oldChecker out state S T K parameter)) :=
      andIntro hz (andIntro (rejectedNormalizer endpoint state parameter hz)
        (rejectedLeafForward endpoint oldChecker out state S T K parameter he' hz hc'))
    obtain ⟨h0⟩ := hzero
    obtain ⟨hr⟩ := hr
    exact ⟨Derivation.implicationElimination
      (addHyp (Derivation.implicationIntroduction h0) _) hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedCheckerInverseGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedCheckerInverseGuardProof
