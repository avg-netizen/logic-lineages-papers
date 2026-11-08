module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingMembershipProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformApplicationTyping InternalOriginalUniformApplicationTypingTargets
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformContextMembership (normalizeData contextMember)
open InternalOriginalUniformContextMembershipEvaluationProof
open InternalOriginalUniformParameterLeaves InternalOriginalUniformParameterLeavesCodecProof
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSupportProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- The membership section has two closed inputs. The original total Object
codec supplies some Gamma at code zero; its value is irrelevant to membership. -/
theorem contextMembershipEvaluation (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (tau : Ty) :
    evaluate (contextMember data.member)
        (List.Vector.ofFn ![typeNumber tau,OrdinaryArithmeticQuotient.contextCode symbols S table]) =
      (decide (tau ∈ S)).toNat := by
  rw [contextMemberEvaluation,hc.2.2.2]
  change memberValue n (List.Vector.ofFn
    ![typeNumber tau,Nat.pair (OrdinaryArithmeticQuotient.contextCode symbols S table) 0]) = _
  obtain ⟨Gamma,hGamma⟩ := actualOriginalUniformParameterCodec.2 (typeNumber tau)
    (Nat.pair (OrdinaryArithmeticQuotient.contextCode symbols S table) 0)
  have hcontext : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (OrdinaryArithmeticQuotient.contextCode symbols S table) = some ((symbols,S),table) := by
    simp only [OrdinaryArithmeticQuotient.contextCode,Encodable.encodek]
  simp only [memberValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    decodedValue,Nat.unpair_pair,hcontext,hGamma,
    InternalStructuralEndpointGuard.membershipValue,
    NumberedNumericDecodingProof.typeNumericRoundTrip tau]

/-- Invoke only the existing original-calculus theorem for a completely
closed binary Program evaluation, then weaken its empty assumption context. -/
theorem binaryNumeral (p : Program 2) (left right out : Nat)
    (he : evaluate p (List.Vector.ofFn ![left,right]) = out) :
    Nonempty (Derivation body Delta
      (graph2 p (numeral out) (numeral left) (numeral right))) := by
  have hx : (fun i => (numeral ((List.Vector.ofFn ![left,right]).get i) : OTerm α)) =
      Fin.cons (numeral left) (Fin.cons (numeral right) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  obtain ⟨h⟩ := InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation
    body 2 p (List.Vector.ofFn ![left,right]) α
  rw [he,hx] at h
  exact ⟨weakenClosed h Delta⟩

/-- The previously proved symbolic slice accepts arbitrary parameter and
Gamma-code terms. Only its contextMember premise is obtained by evaluation. -/
theorem membershipAtParameter (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (tau : Ty) (parameter gammaCode : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (parameterGraph (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode))) :
    Nonempty (Derivation body Delta
      (memberGraph (normalizeData data) (numeral ((decide (tau ∈ S)).toNat))
        (numeral (typeNumber tau)) parameter)) := by
  exact InternalOriginalUniformContextMembershipInternalProof.sliceAccept data.member
    (numeral ((decide (tau ∈ S)).toNat)) (numeral (typeNumber tau)) parameter
    (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) gammaCode hp
    (binaryNumeral (contextMember data.member) (typeNumber tau)
      (OrdinaryArithmeticQuotient.contextCode symbols S table) ((decide (tau ∈ S)).toNat)
      (contextMembershipEvaluation n arity data hc symbols S table tau))

theorem actualOriginalUniformNormalizedMembershipNumeral :
    ActualOriginalUniformNormalizedMembershipNumeral := by
  intro n arity data hc symbols S table tau body α Delta parameter gammaCode
  let P := parameterGraph (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode
  obtain ⟨h⟩ := membershipAtParameter (body := body) (Delta := P :: Delta)
    n arity data hc symbols S table tau parameter gammaCode
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

/-- A false closed arrow-membership test contradicts the supplied internal
output one; a true test supplies codomain membership through subtype closure. -/
theorem codomainMembership (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (hS : SubtypeClosed (fun typ => typ ∈ S))
    (sigma tau : Ty) (parameter gammaCode : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (parameterGraph (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode)))
    (hm : Nonempty (Derivation body Delta
      (memberGraph (normalizeData data) InternalOriginalStepGuard.one
        (numeral (typeNumber (.arrow sigma tau))) parameter))) :
    Nonempty (Derivation body Delta
      (memberGraph (normalizeData data) InternalOriginalStepGuard.one
        (numeral (typeNumber tau)) parameter)) := by
  by_cases ha : Ty.arrow sigma tau ∈ S
  · have ht := NumberedUniverseOperationsProof.arrowCodomain (fun typ => typ ∈ S) hS sigma tau ha
    have hOne : (numeral 1 : OTerm α) = InternalOriginalStepGuard.one := by
      rw [numeral,numeral]
    simpa only [ht,decide_true,Bool.toNat_true,hOne] using
      membershipAtParameter n arity data hc symbols S table tau parameter gammaCode hp
  · have hZero : (numeral 0 : OTerm α) = z := by rw [numeral]
    have hz : Nonempty (Derivation body Delta
        (memberGraph (normalizeData data) z
          (numeral (typeNumber (.arrow sigma tau))) parameter)) := by
      simpa only [ha,decide_false,Bool.toNat_false,hZero] using
        membershipAtParameter n arity data hc symbols S table (.arrow sigma tau) parameter gammaCode hp
    obtain ⟨he⟩ := valueUnique (normalizeData data).member (suc z) z
      (Fin.cons (numeral (typeNumber (.arrow sigma tau))) (Fin.cons parameter Fin.elim0)) hm hz
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

theorem actualOriginalUniformNormalizedCodomainMembership :
    ActualOriginalUniformNormalizedCodomainMembership := by
  intro n arity data hc symbols S table hS body α Delta sigma tau parameter gammaCode
  let P := parameterGraph (OrdinaryArithmeticQuotient.contextCode symbols S table) parameter gammaCode ⊓
    memberGraph (normalizeData data) InternalOriginalStepGuard.one
      (numeral (typeNumber (.arrow sigma tau))) parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := codomainMembership n arity data hc symbols S table hS sigma tau
    parameter gammaCode (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingMembershipProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingMembershipProof
