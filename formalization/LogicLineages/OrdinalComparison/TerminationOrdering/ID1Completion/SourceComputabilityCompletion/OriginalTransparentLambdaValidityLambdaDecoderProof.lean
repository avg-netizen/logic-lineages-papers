module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaDecoderProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open InternalOriginalStepGuard InternalApplicationValidityStackDecoderProof
open OriginalHereditaryValidity OriginalTransparentLambdaValidity

/-- Invert syntax before specializing the dependent result type. This avoids
index elimination through the ordinary/numbered application constructors. -/
theorem lambdaBodyWitness (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (rho : Ty) (q : AuxTerm (Fin n) arity Gamma rho)
    (sigma tau : Ty) (bp : Nat) (hr : rho = .arrow sigma tau)
    (hq : codeNumber (termCode q) = Nat.pair 1 (Nat.pair (typeNumber sigma) bp)) :
    ∃ b : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
      codeNumber (termCode b) = bp := by
  cases q with
  | @lam _ domain codomain b =>
    obtain ⟨hd,he⟩ := Ty.arrow.inj hr
    cases hd
    cases he
    simp only [termCode,codeNumber,Nat.pair_eq_pair,true_and] at hq
    exact ⟨b,hq⟩
  | _ => simp [termCode,codeNumber,Nat.pair_eq_pair] at hq

/-- Literal original lambda syntax at an original arrow type. -/
theorem lambdaWitness (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (sigma tau : Ty) (bp : Nat) :
    (∃ q : AuxTerm (Fin n) arity Gamma (.arrow sigma tau),
      codeNumber (termCode q) = Nat.pair 1 (Nat.pair (typeNumber sigma) bp)) ↔
    (∃ b : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
      codeNumber (termCode b) = bp) := by
  constructor
  · rintro ⟨q,hq⟩
    exact lambdaBodyWitness n arity Gamma _ q sigma tau bp rfl hq
  · rintro ⟨b,hb⟩
    exact ⟨.lam b,by simp [termCode,codeNumber,hb]⟩

theorem lambdaBodySourceWitness (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty)
    (rho : Ty) (q : AuxTerm (Fin n) arity Gamma rho)
    (sigma tau : Ty) (bp : Nat) (hr : rho = .arrow sigma tau)
    (hq : codeNumber (termCode q) = Nat.pair 1 (Nat.pair (typeNumber sigma) bp))
    (hu : universeTest symbols S q = true) :
    (.arrow sigma tau) ∈ S ∧ sigma ∈ S ∧
      (∃ b : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
        codeNumber (termCode b) = bp ∧ universeTest symbols S b = true) := by
  cases q with
  | @lam _ domain codomain b =>
    obtain ⟨hd,he⟩ := Ty.arrow.inj hr
    cases hd
    cases he
    simp only [termCode,codeNumber,Nat.pair_eq_pair,true_and] at hq
    simp only [universeTest,Bool.and_eq_true,decide_eq_true_eq] at hu
    exact ⟨hu.1.1,hu.1.2,b,hq,hu.2⟩
  | _ => simp [termCode,codeNumber,Nat.pair_eq_pair] at hq

/-- The source universe retains outer arrow and actual domain membership.
The body's own universe check supplies codomain membership. -/
theorem lambdaSourceWitness (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma tau : Ty) (bp : Nat) :
    (∃ q : AuxTerm (Fin n) arity Gamma (.arrow sigma tau),
      codeNumber (termCode q) = Nat.pair 1 (Nat.pair (typeNumber sigma) bp) ∧
      universeTest symbols S q = true) ↔
    (.arrow sigma tau) ∈ S ∧ sigma ∈ S ∧
      (∃ b : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
        codeNumber (termCode b) = bp ∧ universeTest symbols S b = true) := by
  constructor
  · rintro ⟨q,hq,hu⟩
    exact lambdaBodySourceWitness n arity symbols S Gamma _ q sigma tau bp rfl hq hu
  · rintro ⟨ht,hd,b,hb,hu⟩
    exact ⟨.lam b,by simp [termCode,codeNumber,hb],by simp [universeTest,ht,hd,hu]⟩

theorem typedLambdaAcceptance (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (sigma tau : Ty) (bp : Nat) :
    (targetValidityValue n arity Gamma
        (Nat.pair (typeNumber (.arrow sigma tau)) (Nat.pair 1 (Nat.pair (typeNumber sigma) bp))) = 1 ↔
      targetValidityValue n arity (sigma :: Gamma) (Nat.pair (typeNumber tau) bp) = 1) ∧
    (sourceValidityValue n arity symbols S Gamma
        (Nat.pair (typeNumber (.arrow sigma tau)) (Nat.pair 1 (Nat.pair (typeNumber sigma) bp))) = 1 ↔
      InternalStructuralEndpointGuard.membershipValue S (typeNumber (.arrow sigma tau)) = 1 ∧
      InternalStructuralEndpointGuard.membershipValue S (typeNumber sigma) = 1 ∧
      sourceValidityValue n arity symbols S (sigma :: Gamma) (Nat.pair (typeNumber tau) bp) = 1) := by
  constructor
  · simpa only [← targetWitness] using lambdaWitness n arity Gamma sigma tau bp
  · have h := lambdaSourceWitness n arity symbols S Gamma sigma tau bp
    simpa only [← sourceWitness,InternalStructuralEndpointGuard.membershipValue,
      NumberedNumericDecodingSupportProof.typeRoundTrip,Option.some.injEq,
      Bool.toNat_eq_one,decide_eq_true_eq] using h

/-- Acceptance of the original target decoder forbids a lambda-tagged raw
value with outer base type or disagreement between outer and payload domains. -/
theorem shapeOfTarget (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) (ht : tagValue value = 1)
    (ha : targetValidityValue n arity Gamma value = 1) : lambdaShapeValue value = 1 := by
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp [targetValidityValue,hd] at ha
  | some q =>
    have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q hd
    rw [← he] at ht ⊢
    obtain ⟨tau,q⟩ := q
    cases q with
    | lam b =>
      simp [lambdaShapeValue,resultTypeValue,InternalApplicationValidityStack.resultTypeValue,
        domainValue,InternalApplicationValidityStack.domainValue,InternalApplicationValidityStack.bodyValue,
        InternalApplicationValidityStack.payloadValue,lambdaCodomainValue,packedNumber,
        termCode,codeNumber,typeNumber,Nat.add_comm 1]
    | _ =>
      simp [tagValue,InternalApplicationValidityStack.tagValue,InternalApplicationValidityStack.payloadValue,
        packedNumber,termCode,codeNumber] at ht

theorem fixedSourceImpliesTarget (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat)
    (hs : sourceValidityValue n arity symbols S Gamma value = 1) :
    targetValidityValue n arity Gamma value = 1 := by
  unfold sourceValidityValue rawCarrierTest decodeUniverse at hs
  unfold targetValidityValue
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp [hd] at hs
  | some q => simp [hd]

/-- Shape and the literal lambda tag reconstruct the raw parent exactly. -/
theorem lambdaReconstruction (value : Nat) (ht : tagValue value = 1)
    (hs : lambdaShapeValue value = 1) :
    Nat.pair (Nat.succ (Nat.pair (domainValue value) (lambdaCodomainValue value)))
      (Nat.pair 1 (Nat.pair (domainValue value) (lambdaBodyPayloadValue value))) = value := by
  have hshape : resultTypeValue value =
      Nat.succ (Nat.pair (domainValue value) (lambdaCodomainValue value)) := by
    simpa [lambdaShapeValue] using hs
  rw [← hshape,← ht]
  simp only [resultTypeValue,InternalApplicationValidityStack.resultTypeValue,tagValue,
    InternalApplicationValidityStack.tagValue,domainValue,InternalApplicationValidityStack.domainValue,
    InternalApplicationValidityStack.bodyValue,lambdaBodyPayloadValue,payloadValue,
    InternalApplicationValidityStack.payloadValue,Nat.pair_unpair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaDecoderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaDecoderProof
