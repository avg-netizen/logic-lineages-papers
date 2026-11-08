module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftResultProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTransportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberCertifiedLift
open InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof InternalOriginalObjectFiberCertifiedLiftResultProof
open InternalOriginalObjectFiberCertifiedLiftSyntaxProof InternalOriginalObjectFiberCertifiedLiftInputProof
open InternalApplicationCertificateConstructors InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalCanonicalFixedWindowVertexDispatchInvariantProof
open InternalPositiveUnfoldingSupportProof InternalTagArithmeticSupportProof
open InternalOriginalObjectFiberSourceDispatchGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationCertificateConstructorsSyntaxProof InternalGraphCompositionSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof GuardedSourceSyntaxProof
open InternalComputabilityApplicationSyntaxProof InternalComputabilityDownwardSyntaxProof
open InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem actualVertex (K : Nat) (p : Selection) (sigma tau : Ty) (x u v : OTerm α)
    (hx : Nonempty (Derivation body Delta (rawTyped p (.arrow sigma tau) x)))
    (hu : Nonempty (Derivation body Delta (rawTyped p sigma u)))
    (hv : Nonempty (Derivation body Delta
      (InternalCanonicalQuotientEdgeApplicationLift.applicationGraph p.canonical v
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x u))) :
    Nonempty (Derivation body Delta
      (InternalCanonicalFixedWindowVertexDispatch.vertexGraph K p.canonical p.oldVertex v (numeral K)
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) u x)) := by
  obtain ⟨ha⟩ := invariantActivation K p.canonical sigma tau _ _ _ u x
    (rawInvariant K p sigma tau x u hx hu)
  obtain ⟨he⟩ := InternalCanonicalFixedWindowVertexDispatchProof.actualInternalCanonicalFixedWindowActiveVertexGraph
    K p.canonical p.oldVertex body α Delta (numeral K)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) u x v
  obtain ⟨hv⟩ := hv
  exact ⟨Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination he ha)) hv⟩

theorem pairedCoordinates (Gamma : List Ty) (out v : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing out (numeral (Encodable.encode Gamma)) v))) :
    Nonempty (Derivation body Delta
      (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma out v)) := by
  obtain ⟨he⟩ := InternalOriginalObjectFiberPathDispatchGraphProof.actualInternalOriginalObjectFiberPairGraph
    Gamma body α Delta out v
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft he) hp⟩

theorem rawOutputTyped (S : List Ty) (p : Selection)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty) (x u v : OTerm α)
    (hx : Nonempty (Derivation body Delta (rawTyped p (.arrow sigma tau) x)))
    (hu : Nonempty (Derivation body Delta (rawTyped p sigma u)))
    (hv : Nonempty (Derivation body Delta
      (InternalCanonicalQuotientEdgeApplicationLift.applicationGraph p.canonical v
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x u))) :
    Nonempty (Derivation body Delta (rawTyped p tau v)) := by
  obtain ⟨he⟩ := InternalCanonicalQuotientEdgeApplicationLiftProof.actualOriginalCanonicalApplicationTypedOutput
    S p.canonical hm hc body sigma tau α Delta x u v
  obtain ⟨hp⟩ := andIntro hx (andIntro hu hv)
  exact ⟨Derivation.implicationElimination he hp⟩

theorem applicationPairCases (Gamma : List Ty) (p : Selection)
    (sigma tau : Ty) (out x u : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Delta
      (InternalOriginalObjectFiberSourceDispatch.pairedApplicationGraph Gamma p.canonical
        out (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x u)))
    (k : ∀ (β : Type) (j : α → β) (Theta : List (Formula β)) (v : OTerm β),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (InternalCanonicalQuotientEdgeApplicationLift.applicationGraph p.canonical v
          (numeral (typeNumber sigma)) (numeral (typeNumber tau)) (x.relabel j) (u.relabel j))) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (out.relabel j) (numeral (Encodable.encode Gamma)) v)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  rw [pairedApplicationEq] at h
  apply pairedCases (Encodable.encode Gamma) (InternalCanonicalQuotientEdgeApplicationLift.actualJ p.canonical)
    out _ psi h
  intro β j Theta v hj hv hp
  apply k β j Theta v hj _ hp
  simpa only [InternalCanonicalQuotientEdgeApplicationLift.applicationGraph,graph4,
    consTermRename,
    numeralRename,
    emptyRename] using hv

/-- All outputs here are the actual supplied object and program outputs. -/
theorem rawTransportCore (S : List Ty) (K : Nat) (Gamma : List Ty) (p : Selection)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (a out other witness lifted x y u v w : OTerm α)
    (ha : Nonempty (Derivation body Delta
      (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma a u)))
    (hx : Nonempty (Derivation body Delta (rawTyped p (.arrow sigma tau) x)))
    (hy : Nonempty (Derivation body Delta (rawTyped p (.arrow sigma tau) y)))
    (hu : Nonempty (Derivation body Delta (rawTyped p sigma u)))
    (hpath : Nonempty (Derivation body Delta (rawPositive p x y witness)))
    (hv : Nonempty (Derivation body Delta
      (InternalCanonicalQuotientEdgeApplicationLift.applicationGraph p.canonical v
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x u)))
    (hw : Nonempty (Derivation body Delta
      (InternalCanonicalQuotientEdgeApplicationLift.applicationGraph p.canonical w
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) y u)))
    (hpv : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing out (numeral (Encodable.encode Gamma)) v)))
    (hpw : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing other (numeral (Encodable.encode Gamma)) w)))
    (hlift : Nonempty (Derivation body Delta
      (programGraph (lift K Gamma p) lifted
        (InternalComputabilityDownward.liftArguments K sigma tau a witness)))) :
    Nonempty (Derivation body Delta
      (transportedOutputs Gamma p tau out other lifted v w)) := by
  obtain ⟨hmapEq⟩ := InternalOriginalObjectFiberPathDispatchGraphProof.actualInternalOriginalObjectFiberActiveGraph
    Gamma (selectedVertex K p) p.oldLift body α Delta (numeral K)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) a u witness lifted
  obtain ⟨ha'⟩ := ha
  obtain ⟨hlift'⟩ := hlift
  have hmap := (⟨Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination hmapEq ha')) hlift'⟩ :
    Nonempty (Derivation body Delta (InternalApplicationPathMap.mapGraph (selectedVertex K p)
      lifted witness (numeral K) (numeral (typeNumber sigma)) (numeral (typeNumber tau)) u)))
  have hpos := InternalCanonicalFixedWindowPathLiftProof.actualInternalCanonicalFixedWindowPositivePathLift
    S p.canonical hm hc K p.oldVertex body sigma tau α Delta
    ![numeral K,numeral (typeNumber sigma),numeral (typeNumber tau),u]
    x y witness v w lifted
    (andIntro (rawInvariant K p sigma tau x u hx hu)
      (andIntro hpath (andIntro (actualVertex K p sigma tau x u v hx hu hv)
        (andIntro (actualVertex K p sigma tau y u w hy hu hw) hmap))))
  exact andIntro (pairedCoordinates Gamma out v hpv)
    (andIntro (pairedCoordinates Gamma other w hpw)
      (andIntro (rawOutputTyped S p hm hc sigma tau x u v hx hu hv)
        (andIntro (rawOutputTyped S p hm hc sigma tau y u w hy hu hw) hpos)))

theorem transportOpenedInputs (S : List Ty) (K : Nat) (Gamma : List Ty) (p : Selection)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S))
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1)
    (sigma tau : Ty) (f g a out other witness lifted x y u : OTerm α)
    (h : Nonempty (Derivation body Delta
      (originalPremises (src K Gamma p) (comp K Gamma p) (lift K Gamma p)
        K sigma tau f g a out other witness lifted)))
    (hi : Nonempty (Derivation body Delta
      (inputData Gamma p sigma tau f g a witness x y u))) :
    Nonempty (Derivation body Delta
      (transportedOutputsExist Gamma p tau out other lifted)) := by
  have hfC := andLeft hi
  have hgC := andLeft (andRight hi)
  have haC := andLeft (andRight (andRight hi))
  have hty := andRight (andRight (andRight hi))
  have hgD := andIntro
    (andIntro (typedAccept K Gamma p (.arrow sigma tau) g y hgC (andLeft (andRight hty)))
      (andRight (andLeft (andLeft (andLeft h)))))
    (objectGuard K Gamma p g a (andLeft hgC) (andLeft haC))
  have hv := applicationResult K Gamma p hw sigma tau f a x u out
    (andLeft (andLeft h)) hfC haC (andLeft (andLeft (andRight h)))
  have hw' := applicationResult K Gamma p hw sigma tau g a y u other
    hgD hgC haC (andRight (andLeft (andRight h)))
  apply applicationPairCases Gamma p sigma tau out x u _ hv
  intro β j Theta v hj hv hpv
  simp only [transportedOutputsExistRename]
  have hi' := renameInto hi j Theta hj
  have h' := renameInto h j Theta hj
  have hw'' := renameInto hw' j Theta hj
  simp only [inputDataRename] at hi'
  simp only [originalPremisesRename] at h'
  rw [pairedApplicationEq] at hw''
  simp only [pairedRename,numeralRename,consTermRename,emptyRename] at hw''
  rw [← pairedApplicationEq] at hw''
  apply applicationPairCases Gamma p sigma tau (other.relabel j) (y.relabel j) (u.relabel j) _ hw''
  intro γ k Xi w hk hww hpw
  simp only [transportedOutputsExistRename]
  have hi'' := renameInto hi' k Xi hk
  have h'' := renameInto h' k Xi hk
  have hv' := renameInto hv k Xi hk
  have hpv' := renameInto hpv k Xi hk
  simp only [inputDataRename] at hi''
  simp only [originalPremisesRename] at h''
  simp only [applicationGraphRename,numeralRename] at hv'
  simp only [graph2Rename,numeralRename] at hpv'
  have ht := andRight (andRight (andRight hi''))
  apply transportedOutputsIntro Gamma p tau _ _ _ (v.relabel k) w
  exact rawTransportCore S K Gamma p hm hc sigma tau _ _ _ _ _ _ _ _ _ _
    (andLeft (andRight (andRight hi'')))
    (andLeft ht) (andLeft (andRight ht)) (andLeft (andRight (andRight ht)))
    (andRight (andRight (andRight ht))) hv' hww hpv' hpw
    (andRight (andRight h''))

theorem rawTransport (S : List Ty) (K : Nat) (Gamma : List Ty) (p : Selection)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S))
    (hw : evaluate p.window (List.Vector.ofFn ![K]) = 1)
    (sigma tau : Ty) (f g a out other witness lifted : OTerm α)
    (h : Nonempty (Derivation body Delta
      (fiberPremises (src K Gamma p) (comp K Gamma p) (lift K Gamma p)
        K Gamma sigma tau f g a out other witness lifted))) :
    Nonempty (Derivation body Delta
      (transportedOutputsExist Gamma p tau out other lifted)) := by
  have hi := inputExtract K Gamma p hw sigma tau f g a witness
    (andLeft (andLeft (andLeft h))) (andRight (andLeft (andLeft h))) (andRight h)
  apply inputCases Gamma p sigma tau f g a witness _ hi
  intro β j Theta x y u hj hi'
  simp only [transportedOutputsExistRename]
  have h' := renameInto (andLeft h) j Theta hj
  simp only [originalPremisesRename] at h'
  exact transportOpenedInputs S K Gamma p hm hc hw sigma tau _ _ _ _ _ _ _ x y u h' hi'

theorem actualInternalOriginalObjectFiberRawTransport :
    InternalOriginalObjectFiberCertifiedLiftTargets.ActualInternalOriginalObjectFiberRawTransport := by
  intro S K Gamma p hm hc hw body α Delta sigma tau f g a out other witness lifted
  let pre := fiberPremises (src K Gamma p) (comp K Gamma p) (lift K Gamma p)
    K Gamma sigma tau f g a out other witness lifted
  obtain ⟨h⟩ := rawTransport (body := body) (Delta := pre :: Delta)
    S K Gamma p hm hc hw sigma tau f g a out other witness lifted
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTransportProof
