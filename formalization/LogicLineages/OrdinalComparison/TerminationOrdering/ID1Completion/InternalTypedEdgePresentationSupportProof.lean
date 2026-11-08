module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalTypedEdgePresentation InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof
open InternalPositiveUnfoldingSupportProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Recover the new membership graph and the unchanged canonical typed
wrapper's actual source-validity, raw-tag and old-typed graphs. -/
theorem typedComponents (data : Data) (value typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (typed data value typ))) :
    Nonempty (Derivation body Gamma
      (graph1 data.member (suc z) typ ⊓
        InternalOriginalTypedCarrier.requirements data.validity data.oldTyped value typ)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons typ Fin.elim0)
  have hc := conjunctionRecover (membershipAt data.member)
    (InternalOriginalTypedCarrier.checker data.validity data.oldTyped) xs h
  exact andIntro
    (InternalOriginalTypedCarrierSupportProof.atRecover data.member 1 (suc z) xs (andLeft hc))
    (InternalOriginalTypedCarrierSupportProof.checkerRecover data.validity data.oldTyped
      value typ (andRight hc))

/-- Recover source validity BEFORE any source tag graph is known. This avoids
assuming the very raw-tag witness that representative transport must derive. -/
theorem stepSourceValidity (data : Data) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph3 (stepChecker data) (suc z) s t k))) :
    Nonempty (Derivation body Gamma (graph1 data.validity.sourceValid (suc z) s)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have ho := conjunctionRecover (InternalOriginalStepGuard.guards data.validity)
    (InternalApplicationStepPeel.checker (endpoint data) data.oldEdge.stepProgram) xs h
  have hg := conjunctionRecover (InternalOriginalStepGuard.sourceAt data.validity)
    (InternalAcceptance.conjunction (InternalOriginalStepGuard.targetAt data.validity)
      InternalOriginalStepGuard.sameOuterTypes) xs (andLeft ho)
  exact InternalOriginalStepGuardSupportProof.atRecover data.validity.sourceValid 0
    (suc z) xs (andLeft hg)

/-- Only CLOSED numeral inputs are reflected by the already proved original
numeral-evaluation theorem. No symbolic graph follows from calibration. -/
theorem unaryNumeral (p : Program 1) (input output : Nat)
    (h : evaluate p (List.Vector.ofFn ![input]) = output) :
    Nonempty (Derivation body Gamma (graph1 p (numeral output) (numeral input))) := by
  have hv : (fun i => (numeral ((List.Vector.ofFn ![input]).get i) : OTerm α)) =
      Fin.cons (numeral input) Fin.elim0 := by
    funext i
    exact Fin.cases rfl (fun q => Fin.elim0 q) i
  obtain ⟨d⟩ := InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation
    body 1 p (List.Vector.ofFn ![input]) α
  rw [h,hv] at d
  exact ⟨weakenClosed d Gamma⟩

theorem membershipEvaluation (S : List Ty) (member : Program 1)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S member) (tau : Ty) :
    evaluate member (List.Vector.ofFn ![typeNumber tau]) = (decide (tau ∈ S)).toNat := by
  rw [hm]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,
    InternalStructuralEndpointGuard.membershipValue,NumberedNumericDecodingProof.typeNumericRoundTrip tau]

/-- Arrow membership is not assumed externally. If it fails, the actual
member(arrow)=0 closed graph contradicts the internally exposed output one. -/
theorem codomainMembership (S : List Ty) (member : Program 1)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (ha : Nonempty (Derivation body Gamma
      (graph1 member (suc z) (numeral (typeNumber (.arrow sigma tau)))))) :
    Nonempty (Derivation body Gamma (graph1 member (suc z) (numeral (typeNumber tau)))) := by
  by_cases hmem : Ty.arrow sigma tau ∈ S
  · have ht := NumberedUniverseOperationsProof.arrowCodomain (fun typ => typ ∈ S) hc sigma tau hmem
    apply unaryNumeral member (typeNumber tau) 1
    simpa only [ht,decide_true,Bool.toNat_true] using membershipEvaluation S member hm tau
  · have hz : evaluate member (List.Vector.ofFn ![typeNumber (.arrow sigma tau)]) = 0 := by
      simpa only [hmem,decide_false,Bool.toNat_false] using membershipEvaluation S member hm (.arrow sigma tau)
    obtain ⟨he⟩ := valueUnique member (suc z) z
      (Fin.cons (numeral (typeNumber (.arrow sigma tau))) Fin.elim0) ha
      (unaryNumeral member (typeNumber (.arrow sigma tau)) 0 hz)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

theorem arrowNumeral (sigma tau : Ty) :
    Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode (numeral (typeNumber (.arrow sigma tau)))
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)))) := by
  have ha : evaluate InternalListCodec.consCode
      (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) := by
    exact InternalListCodecEvaluationProof.consEvaluation (typeNumber sigma) (typeNumber tau)
  have hv : (fun i => (numeral ((List.Vector.ofFn ![typeNumber sigma,typeNumber tau]).get i) : OTerm α)) =
      Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau)) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  obtain ⟨d⟩ := InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation
    body 2 InternalListCodec.consCode (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) α
  rw [ha,hv] at d
  exact ⟨weakenClosed d Gamma⟩

/-- Concrete shared-AST endpoint presentation in an arbitrary internal context.
Raw source/target validity and all tag graphs are derived, never assumed. -/
theorem presentation (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate s t k : OTerm α)
    (hp : Nonempty (Derivation body Gamma (premises data sigma tau x y a certificate s t k))) :
    Nonempty (Derivation body Gamma (requirements data sigma tau s t a)) := by
  have hx := typedComponents data x (numeral (typeNumber (.arrow sigma tau))) (andLeft hp)
  have ha := typedComponents data a (numeral (typeNumber sigma)) (andLeft (andRight hp))
  have hedge := InternalQuotientEdgeCheckerSupportProof.checkerRecover (edgeData data)
    x y certificate s t k (andLeft (andRight (andRight hp)))
    (andRight (andRight (andRight hp)))
  have hstep : Nonempty (Derivation body Gamma (graph3 (stepChecker data) (suc z) s t k)) :=
    andLeft hedge
  have hsource := stepSourceValidity data s t k hstep
  have hsourceTag := InternalRepresentativeTagSupportProof.tagBackward
    data.validity.sourceValid data.oldEdge.sourceRepresentative
    (numeral (typeNumber (.arrow sigma tau))) x s
    (andIntro hsource (andLeft (andRight hedge)))
    (andLeft (andRight (andRight hx)))
  have htagged := InternalOriginalStepGuardSupportProof.taggedRecover data.validity
    (InternalApplicationStepPeel.checker (endpoint data) data.oldEdge.stepProgram)
    (numeral (typeNumber (.arrow sigma tau))) s t k hsourceTag hstep
  have htags : Nonempty (Derivation body Gamma
      (InternalStructuralEndpointGuard.tagGraphs
        (numeral (typeNumber (.arrow sigma tau))) (numeral (typeNumber sigma)) s t a)) :=
    andIntro hsourceTag
      (andIntro (andLeft (andRight (andRight htagged))) (andLeft (andRight (andRight ha))))
  have har := arrowNumeral (body := body) (Gamma := Gamma) (α := α) sigma tau
  have hmember := codomainMembership S data.member hm hc sigma tau (andLeft hx)
  have hendpoint := InternalStructuralEndpointGuardSupportProof.endpointAccept data.validity
    data.member (numeral (typeNumber (.arrow sigma tau)))
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) s t a har
    (andIntro hsource (andIntro (andLeft (andRight htagged))
      (andIntro (andLeft (andRight ha)) (andIntro htags hmember))))
  exact andIntro har (andIntro hendpoint htags)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
