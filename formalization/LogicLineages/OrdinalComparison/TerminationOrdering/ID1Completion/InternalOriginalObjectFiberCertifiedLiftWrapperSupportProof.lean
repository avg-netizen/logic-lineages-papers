module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberCertifiedLift
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open GammaGuardedSourceGraphSupportProof GuardedSourceGraphSupportProof
open InternalOriginalObjectFiberSourceDispatchGraphProof SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

 theorem applyImp {a b : Formula α} (h : Nonempty (Derivation body Delta (a.imp b)))
    (ha : Nonempty (Derivation body Delta a)) : Nonempty (Derivation body Delta b) := by
  obtain ⟨h⟩ := h; obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination h ha⟩

 theorem functionFiber (K : Nat) (Gamma : List Ty) (p : Selection) (f a : OTerm α)
    (hg : Nonempty (Derivation body Delta (InternalComputabilityApplication.guarded (comp K Gamma p) f a)))
    (ha : Nonempty (Derivation body Delta (argumentFiber Gamma a))) :
    Nonempty (Derivation body Delta (argumentFiber Gamma f)) := by
  have h := conjunctionRecover _ _ ![f,a] hg
  have h' := conjunctionRecover _ _ ![f,a] (andRight h)
  have hx := InternalStructuralEndpointGuardSupportProof.sameRightRecover
    (GammaGuardedSource.atInput InternalUnpair.left 0)
    (GammaGuardedSource.atInput InternalUnpair.left 1)
    (numeral (Encodable.encode Gamma)) ![f,a] (andRight h')
    (atInputValue InternalUnpair.left 1 _ ![f,a] ha)
  exact atInputRecover InternalUnpair.left 0 _ ![f,a] hx

 theorem basePositiveRecover (K : Nat) (Gamma : List Ty) (p : Selection) (f g witness : OTerm α)
    (hp : Nonempty (Derivation body Delta (InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness))) :
    Nonempty (Derivation body Delta (programGraph
      (GammaGuardedSource.basePositive (patchedSource K Gamma p).positive InternalUnpair.left)
      (suc z) ![numeral K,f,g,witness])) :=
  GammaGuardedSourceBranchProof.guardedPositiveRecover _ _ _ _ _ hp

 theorem sameLeftRecover {n : Nat} (p q : Program n) (value : OTerm α) (xs : Fin n → OTerm α)
    (he : Nonempty (Derivation body Delta (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hp : Nonempty (Derivation body Delta (programGraph p value xs))) :
    Nonempty (Derivation body Delta (programGraph q value xs)) := by
  apply programCases q xs _
  intro β j Theta right hj hr
  simp only [programRename]
  have he' := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  have hp' := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [programRename, InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel] at he' hp'
  obtain ⟨hEq⟩ := InternalEqualityTestProof.equalityOfAcceptance (value.relabel j) right
    (binaryRecover InternalEqualityTest.equalityTest p q (suc z) (value.relabel j) right
      (fun i => (xs i).relabel j) he' hp' hr)
  exact outputTransport q right (value.relabel j) (fun i => (xs i).relabel j)
    ⟨InternalTagArithmeticSupportProof.symm hEq⟩ hr

 theorem targetFiber (K : Nat) (Gamma : List Ty) (p : Selection) (f g witness : OTerm α)
    (hp : Nonempty (Derivation body Delta (InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness)))
    (hf : Nonempty (Derivation body Delta (argumentFiber Gamma f))) :
    Nonempty (Derivation body Delta (argumentFiber Gamma g)) := by
  have hb := conjunctionRecover _ _ ![numeral K,f,g,witness] (basePositiveRecover K Gamma p f g witness hp)
  have hg := sameLeftRecover (GammaGuardedSource.atInput InternalUnpair.left 1)
    (GammaGuardedSource.atInput InternalUnpair.left 2) (numeral (Encodable.encode Gamma))
    ![numeral K,f,g,witness] (andRight hb)
    (atInputValue InternalUnpair.left 1 _ ![numeral K,f,g,witness] hf)
  exact atInputRecover InternalUnpair.left 2 _ ![numeral K,f,g,witness] hg

 theorem patchedTypedIff (K : Nat) (Gamma : List Ty) (p : Selection) (tau : Ty) (object payload : OTerm α)
    (hc : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload))) :
    Nonempty (Derivation body Delta ((programGraph (patchedComp K Gamma p).typed (suc z)
      ![numeral K,numeral (typeNumber tau),object]).iff (rawTyped p tau payload))) := by
  exact applyImp (actualInternalOriginalObjectSourceTypedGraph K Gamma p.canonical p.oldComp.typed body α Delta
    (numeral K) (numeral (typeNumber tau)) object payload (suc z))
    (andIntro (by simpa only [equalEqn] using (show Nonempty (Derivation body Delta (eqn (numeral K) (numeral K))) from ⟨InternalTagArithmeticSupportProof.refl _⟩)) hc)

 theorem typedRecover (K : Nat) (Gamma : List Ty) (p : Selection) (tau : Ty) (object payload : OTerm α)
    (hc : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload)))
    (ht : Nonempty (Derivation body Delta (InternalComputabilityApplication.typed (comp K Gamma p) tau (numeral K) object))) :
    Nonempty (Derivation body Delta (rawTyped p tau payload)) := by
  have h := conjunctionRecover _ _ ![numeral K,numeral (typeNumber tau),object] ht
  have h' := conjunctionRecover _ _ ![numeral K,numeral (typeNumber tau),object] (andLeft h)
  exact applyImp (andLeft (patchedTypedIff K Gamma p tau object payload hc)) (andLeft h')

 theorem tagValue (K : Nat) (Gamma : List Ty) (p : Selection) (tau : Ty) (object payload : OTerm α)
    (hc : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload)))
    (ht : Nonempty (Derivation body Delta (rawTyped p tau payload))) :
    Nonempty (Derivation body Delta (programGraph InternalOriginalObjectFiberSourceDispatch.tag
      (numeral (typeNumber tau)) ![numeral K,object])) := by
  have factors := InternalCanonicalDescentSelectionInternalProof.typedRecover
    p.canonical.oldEdge.targetRepresentative (InternalCanonicalDescentSelection.validity p.canonical).sourceValid
    p.canonical.member payload (numeral (typeNumber tau)) ht
  exact unaryValue InternalUnpair.left _ _ payload ![numeral K,object]
    (andLeft (andRight (andRight factors)))
    (unaryValue InternalUnpair.right (.projection 1) payload object ![numeral K,object]
      (andRight hc) (projectionValue 1 ![numeral K,object]))

 theorem baseTypedAccept (K : Nat) (Gamma : List Ty) (p : Selection) (tau : Ty) (object payload : OTerm α)
    (hc : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload)))
    (ht : Nonempty (Derivation body Delta (rawTyped p tau payload))) :
    Nonempty (Derivation body Delta (programGraph
      (GammaGuardedSource.baseTyped (patchedComp K Gamma p).typed InternalOriginalObjectFiberSourceDispatch.valid)
      (suc z) ![numeral K,numeral (typeNumber tau),object])) :=
  conjunctionAccept _ _ _
    (applyImp (andRight (patchedTypedIff K Gamma p tau object payload hc)) ht)
    (atInputValue InternalOriginalObjectFiberSourceDispatch.valid 2 _ _
      (InternalCanonicalFixedWindowVertexDispatchSupportProof.constantValue 1 1 ![object]))

 theorem typedAccept (K : Nat) (Gamma : List Ty) (p : Selection) (tau : Ty) (object payload : OTerm α)
    (hc : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload)))
    (ht : Nonempty (Derivation body Delta (rawTyped p tau payload))) :
    Nonempty (Derivation body Delta (InternalComputabilityApplication.typed (comp K Gamma p) tau (numeral K) object)) :=
  guardedTypedAccept _ _ (numeral (typeNumber tau)) (numeral K) (numeral (typeNumber tau)) object
    (tagValue K Gamma p tau object payload hc ht) (baseTypedAccept K Gamma p tau object payload hc ht)
    ⟨InternalTagArithmeticSupportProof.refl _⟩

 theorem patchedPositiveIff (K : Nat) (Gamma : List Ty) (p : Selection) (f g x y witness : OTerm α)
    (hf : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x)))
    (hg : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma g y))) :
    Nonempty (Derivation body Delta ((programGraph (patchedSource K Gamma p).positive (suc z)
      ![numeral K,f,g,witness]).iff (rawPositive p x y witness))) :=
  applyImp (actualInternalOriginalObjectSourcePositiveGraph K Gamma p.canonical p.oldSource.positive body α Delta
    (numeral K) f g x y witness (suc z)) (andIntro (by simpa only [equalEqn] using (show Nonempty (Derivation body Delta (eqn (numeral K) (numeral K))) from ⟨InternalTagArithmeticSupportProof.refl _⟩)) (andIntro hf hg))

 theorem positiveRecover (K : Nat) (Gamma : List Ty) (p : Selection) (f g x y witness : OTerm α)
    (hf : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x)))
    (hg : Nonempty (Derivation body Delta (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma g y)))
    (hp : Nonempty (Derivation body Delta (InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness))) :
    Nonempty (Derivation body Delta (rawPositive p x y witness)) :=
  applyImp (andLeft (patchedPositiveIff K Gamma p f g x y witness hf hg))
    (andLeft (conjunctionRecover _ _ _ (basePositiveRecover K Gamma p f g witness hp)))

 theorem objectGuard (K : Nat) (Gamma : List Ty) (p : Selection) (f a : OTerm α)
    (hf : Nonempty (Derivation body Delta (argumentFiber Gamma f)))
    (ha : Nonempty (Derivation body Delta (argumentFiber Gamma a))) :
    Nonempty (Derivation body Delta (InternalComputabilityApplication.guarded (comp K Gamma p) f a)) :=
  guardAccept _ _ (numeral (Encodable.encode Gamma)) (numeral (Encodable.encode Gamma)) f a hf ha
    (InternalCanonicalFixedWindowVertexDispatchSupportProof.constantValue 1 1 ![f])
    (InternalCanonicalFixedWindowVertexDispatchSupportProof.constantValue 1 1 ![a]) ⟨InternalTagArithmeticSupportProof.refl _⟩

 theorem positiveAccept (K : Nat) (Gamma : List Ty) (p : Selection)
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1)
    (tau : Ty) (out other lifted rawOut rawOther : OTerm α)
    (h : Nonempty (Derivation body Delta (transportedOutputs Gamma p tau out other lifted rawOut rawOther))) :
    Nonempty (Derivation body Delta (InternalAccessibilityRules.certificate (src K Gamma p) false K out other lifted)) := by
  let typed := GammaGuardedSource.baseTyped (patchedComp K Gamma p).typed InternalOriginalObjectFiberSourceDispatch.valid
  let positive := GammaGuardedSource.basePositive (patchedSource K Gamma p).positive InternalUnpair.left
  let tag := InternalOriginalObjectFiberSourceDispatch.tag
  let typ : OTerm α := numeral (typeNumber tau)
  let xs := ![numeral K,out,other,lifted]
  have ho := andLeft h
  have hr := andLeft (andRight h)
  have hto := andLeft (andRight (andRight h))
  have htr := andLeft (andRight (andRight (andRight h)))
  have hp := andRight (andRight (andRight (andRight h)))
  have htagO := tagValue K Gamma p tau out rawOut ho hto
  have htagR := tagValue K Gamma p tau other rawOther hr htr
  have hbaseO := baseTypedAccept K Gamma p tau out rawOut ho hto
  have hbaseR := baseTypedAccept K Gamma p tau other rawOther hr htr
  have hpositive : Nonempty (Derivation body Delta (programGraph positive (suc z) xs)) :=
    conjunctionAccept _ _ xs
      (applyImp (andRight (patchedPositiveIff K Gamma p out other rawOut rawOther lifted ho hr)) hp)
      (sameGammaAccept InternalUnpair.left 1 2 (numeral (Encodable.encode Gamma))
        (numeral (Encodable.encode Gamma)) xs (andLeft ho) (andLeft hr) ⟨InternalTagArithmeticSupportProof.refl _⟩)
  have hactive : Nonempty (Derivation body Delta (programGraph (GuardedSource.activation typed tag p.window) (suc z) xs)) :=
    conjunctionAccept _ _ xs
      (windowAtAccept p.window (numeral K) out other lifted (GuardedSourceCertificateProof.windowNumeral p.window K hw))
      (sourceTypedAccept typed tag typ (numeral K) out other lifted htagO hbaseO)
  have htarget : Nonempty (Derivation body Delta (programGraph (GuardedSource.targetTyped typed tag) (suc z) xs)) := by
    apply compositionValue typed ![.projection 0,GuardedSource.rightTag tag,.projection 2]
      (suc z) xs ![numeral K,typ,other] hbaseR
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (rightTagValue tag typ (numeral K) out other lifted htagR)
        (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) i
  have hsame : Nonempty (Derivation body Delta (programGraph (GuardedSource.sameTag tag) (suc z) xs)) := by
    apply compositionValue InternalEqualityTest.equalityTest ![GuardedSource.leftTag tag,GuardedSource.rightTag tag]
      (suc z) xs ![typ,typ] (InternalEqualityTestCompositionProof.equalityOfEqual typ typ ⟨InternalTagArithmeticSupportProof.refl _⟩)
    intro i
    exact Fin.cases (leftTagValue tag typ (numeral K) out other lifted htagO)
      (Fin.cases (rightTagValue tag typ (numeral K) out other lifted htagR) (fun q => Fin.elim0 q)) i
  exact InternalAcceptanceBranchProof.successorBranchIntro (GuardedSource.activation typed tag p.window)
    positive (GuardedSource.acceptedTarget positive typed tag) (suc z) z xs hactive
    (conjunctionAccept _ _ xs hpositive (conjunctionAccept _ _ xs htarget hsame))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
