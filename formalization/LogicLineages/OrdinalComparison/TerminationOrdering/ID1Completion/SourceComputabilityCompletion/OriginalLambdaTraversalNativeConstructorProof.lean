module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeConstructorProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientApplication
open OriginalLambdaCanonical OriginalLambdaTraversal OriginalLambdaTraversalSemanticProof
open OriginalLambdaTraversalWeightProof
open InternalRepresentativeFoldCalibrationSupportProof (applicationSelectors)

theorem applicationTag {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) :
    tagValue (packedNumber (applicationPacked f a)) = 2 := by
  simp [tagValue, OriginalHereditaryValidity.tagValue, InternalApplicationValidityStack.tagValue,
    InternalApplicationValidityStack.payloadValue, applicationPacked, packedNumber, termCode, codeNumber]

theorem applicationFields {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) :
    domainValue (packedNumber (applicationPacked f a)) = typeNumber sigma ∧
    resultTypeValue (packedNumber (applicationPacked f a)) = typeNumber tau ∧
    functionChildValue (packedNumber (applicationPacked f a)) = packedNumber ⟨.arrow sigma tau,f⟩ ∧
    argumentChildValue (packedNumber (applicationPacked f a)) = packedNumber ⟨sigma,a⟩ :=
  applicationSelectors f a

theorem lambdaSelectors {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (b : AuxTerm (Fin n) arity (sigma :: Gamma) tau) :
    tagValue (packedNumber (lambdaPacked b)) = 1 ∧
    domainValue (packedNumber (lambdaPacked b)) = typeNumber sigma ∧
    lambdaCodomainValue (packedNumber (lambdaPacked b)) = typeNumber tau ∧
    lambdaBodyValue (packedNumber (lambdaPacked b)) = packedNumber ⟨tau,b⟩ := by
  simp [tagValue, domainValue, lambdaCodomainValue, lambdaBodyValue,
    OriginalHereditaryValidity.tagValue, OriginalHereditaryValidity.domainValue,
    OriginalHereditaryValidity.lambdaCodomainValue, OriginalHereditaryValidity.lambdaBodyValue,
    OriginalHereditaryValidity.lambdaBodyPayloadValue, OriginalHereditaryValidity.resultTypeValue,
    OriginalHereditaryValidity.payloadValue, InternalApplicationValidityStack.tagValue,
    InternalApplicationValidityStack.domainValue, InternalApplicationValidityStack.resultTypeValue,
    InternalApplicationValidityStack.bodyValue, InternalApplicationValidityStack.payloadValue,
    lambdaPacked, packedNumber, termCode, codeNumber, typeNumber, Nat.add_comm 1]

theorem applicationPayloadLess {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) :
    payloadValue (packedNumber ⟨.arrow sigma tau,f⟩) <
        payloadValue (packedNumber (applicationPacked f a)) ∧
    payloadValue (packedNumber ⟨sigma,a⟩) <
        payloadValue (packedNumber (applicationPacked f a)) := by
  have h := applicationFuelBound (packedNumber (applicationPacked f a)) (applicationTag f a)
  have hs := applicationFields f a
  rw [hs.2.2.1, hs.2.2.2] at h
  simp only [fuelValue] at h
  constructor <;> omega

theorem lambdaPayloadLess {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (b : AuxTerm (Fin n) arity (sigma :: Gamma) tau) :
    payloadValue (packedNumber ⟨tau,b⟩) < payloadValue (packedNumber (lambdaPacked b)) := by
  have hs := lambdaSelectors b
  have h := lambdaFuelBound (packedNumber (lambdaPacked b)) hs.1
  rw [hs.2.2.2] at h
  simp only [fuelValue] at h
  omega

theorem childContext (value parameter : Nat) :
    (Nat.unpair (childParameterValue value parameter)).1 = (Nat.unpair parameter).1 := by
  simp [childParameterValue, OriginalHereditaryValidity.childParameterValue]

theorem childGamma {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (b : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (parameter : Nat) (hg : Encodable.encode Gamma = (Nat.unpair parameter).2) :
    Encodable.encode (sigma :: Gamma) =
      (Nat.unpair (childParameterValue (packedNumber (lambdaPacked b)) parameter)).2 := by
  have hd := (lambdaSelectors b).2.1
  simp only [childParameterValue, OriginalHereditaryValidity.childParameterValue,
    Nat.unpair_pair, OriginalContextExtensionCalibrationProof.contextEncoding, hd, hg]
  omega

theorem semanticApplication {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (leaf : Nat → Nat → Nat)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (parameter : Nat) :
    semanticFold leaf (packedNumber (applicationPacked f a)) parameter =
      applicationValue (typeNumber sigma) (typeNumber tau)
        (semanticFold leaf (packedNumber ⟨.arrow sigma tau,f⟩) parameter)
        (semanticFold leaf (packedNumber ⟨sigma,a⟩) parameter) := by
  have hs := applicationFields f a
  rw [semanticEquation, if_pos (applicationTag f a), hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

theorem semanticLambda {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (leaf : Nat → Nat → Nat)
    (b : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (parameter : Nat) :
    semanticFold leaf (packedNumber (lambdaPacked b)) parameter =
      lambdaValue (typeNumber sigma) (typeNumber tau)
        (semanticFold leaf (packedNumber ⟨tau,b⟩)
          (childParameterValue (packedNumber (lambdaPacked b)) parameter)) := by
  have hs := lambdaSelectors b
  have hn : tagValue (packedNumber (lambdaPacked b)) ≠ 2 := by omega
  rw [semanticEquation, if_neg hn, if_pos hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

theorem applicationRepresentative (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S)) (Gamma : List Ty)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse symbols S f) (ha : InUniverse symbols S a) :
    applicationValue (typeNumber sigma) (typeNumber tau)
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩)
      (representativeCode symbols S ⟨sigma,a⟩) =
        representativeCode symbols S (applicationPacked f a) :=
  (NumberedApplicationFactorizationProof.actualRepresentativeApplicationFactorization
    n arity symbols S hS Gamma sigma tau f a hf ha).symm

theorem lambdaRepresentative (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (hS : SubtypeClosed (fun rho => rho ∈ S)) (Gamma : List Ty)
    (sigma tau : Ty) (b : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (hb : InUniverse symbols S (.lam b)) :
    lambdaValue (typeNumber sigma) (typeNumber tau)
      (representativeCode symbols S ⟨tau,b⟩) =
        representativeCode symbols S (lambdaPacked b) :=
  (OriginalLambdaCanonicalProof.actualOriginalLambdaRepresentativeFactorization
    n arity symbols S hS Gamma sigma tau b hb).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeConstructorProof
