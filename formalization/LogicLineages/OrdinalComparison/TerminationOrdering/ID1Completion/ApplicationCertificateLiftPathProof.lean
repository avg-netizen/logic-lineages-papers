module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedNumericCarrier NumberedNumericDecoding NumberedTypedCarrier
open NumberedQuotientPathCertificates ApplicationCertificateLiftPath

theorem positiveFiber (n : Nat) (arity : Fin n → Nat) (context f g certificate : Nat)
    (Gamma : List Ty) (x : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hf : Encodable.decode (α := ContextUniform.Object) f = some (Gamma,x))
    (hc : Encodable.decode context = some ctx)
    (h : ContextUniform.positiveValue n arity (List.Vector.ofFn ![context,f,g,certificate]) = 1) :
    ∃ y : Nat, Encodable.decode (α := ContextUniform.Object) g = some (Gamma,y) ∧
      positivePathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y certificate = true := by
  cases hg : Encodable.decode (α := ContextUniform.Object) g with
  | none => simp [ContextUniform.positiveValue,hf,hg] at h
  | some obj =>
    obtain ⟨Delta,y⟩ := obj
    by_cases he : Gamma = Delta
    · subst Delta
      refine ⟨y,rfl,?_⟩
      simpa [ContextUniform.positiveValue,OrdinaryArithmeticQuotient.positiveValue,hf,hg,hc] using h
    · simp [ContextUniform.positiveValue,hf,hg,he] at h

theorem canonicalTypedTerm (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (tau : Ty) (value : Nat)
    (h : typedCanonicalCarrierTest n arity symbols S Gamma tau value = true) :
    ∃ q : AuxTerm (Fin n) arity Gamma tau,
      InUniverse symbols S q ∧
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma) = value ∧
      representativeCode symbols S ⟨tau,q⟩ = value := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [typedCanonicalCarrierTest,hd] at h
  | some q =>
    obtain ⟨sigma,q⟩ := q
    have hh : sigma = tau ∧ representativeCode symbols S ⟨sigma,q⟩ = value := by
      simpa [typedCanonicalCarrierTest,hd] using h
    obtain ⟨rfl,hr⟩ := hh
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value ⟨sigma,q⟩).mp hd
    exact ⟨q,hq.2,hq.1,hr⟩

theorem builderCalibration (n : Nat) (arity : Fin n → Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (Gamma : List Ty) (sigma tau : Ty) (context domain codomain f a x y : Nat)
    (hctx : Encodable.decode context = some ctx)
    (hd : decodeType domain = some sigma) (he : decodeType codomain = some tau)
    (hfo : Encodable.decode (α := ContextUniform.Object) f = some (Gamma,x))
    (hao : Encodable.decode (α := ContextUniform.Object) a = some (Gamma,y))
    (ft : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (arg : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse ctx.1.1 ctx.1.2 ft) (ha : InUniverse ctx.1.1 ctx.1.2 arg)
    (hfr : representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,ft⟩ = x)
    (har : representativeCode ctx.1.1 ctx.1.2 ⟨sigma,arg⟩ = y) :
    ApplicationResultBuilder.resultValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a]) =
      ContextUniform.objectCode Gamma (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app ft arg⟩) := by
  have happ := NumberedNumericApplicationProof.canonicalApplicationCalibration n arity
    ctx.1.1 ctx.1.2 hclosed Gamma sigma tau ft arg hf ha
  rw [hfr,har] at happ
  have ho : ApplicationResultBuilder.resultOption n arity
      (List.Vector.ofFn ![context,domain,codomain,f,a]) =
      some (ContextUniform.objectCode Gamma (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app ft arg⟩)) := by
    simpa [ApplicationResultBuilder.resultOption,hfo,hao,
      OrdinaryArithmeticApplication.decodedApplication,hctx,hd,he,
      NumberedQuotientApplication.applicationPacked] using congrArg
        (Option.map (ContextUniform.objectCode Gamma)) happ
  exact ((ApplicationResultBuilderProof.partialTotal n arity _ _).mp ho).2.symm

theorem actualOriginalPositiveLift : ApplicationCertificateLiftPathTargets.ActualOriginalPositiveLift := by
  intro n arity context domain codomain f g a certificate hactive hpositive
  rcases hactive with ⟨hW,hF,hA,hG⟩
  obtain ⟨ctx,hctx,hclosed⟩ := (GuardCalibrationProof.actualValidWindowCalibration n context).1.mp hW
  obtain ⟨sigma,hs,hsc⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal domain
  obtain ⟨tau,ht,htc⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal codomain
  have harr : decodeType (ApplicationDomain.arrowCode domain codomain) = some (.arrow sigma tau) := by
    rw [← hsc,← htc]
    exact NumberedNumericDecodingProof.typeNumericRoundTrip (.arrow sigma tau)
  obtain ⟨Gamma,x,argument,hfo,hao⟩ := (JointGammaDomainProof.actualGuardCalibration.1 f a).mp hG
  obtain ⟨y,hgo,hpath⟩ := positiveFiber n arity context f g certificate Gamma x ctx hfo hctx hpositive
  have hF' := ApplicationDomainProof.typedFiberCheck n arity context
    (ApplicationDomain.arrowCode domain codomain) f Gamma x ctx (.arrow sigma tau) hfo hctx harr hF
  have hA' := ApplicationDomainProof.typedFiberCheck n arity context domain a Gamma argument ctx sigma hao hctx hs hA
  have hGtyped := PositiveTypedCalibrationProof.actualTypedSuccessor n arity context
    (ApplicationDomain.arrowCode domain codomain) f g certificate hW hF hpositive
  have hG' := ApplicationDomainProof.typedFiberCheck n arity context
    (ApplicationDomain.arrowCode domain codomain) g Gamma y ctx (.arrow sigma tau) hgo hctx harr hGtyped
  obtain ⟨ft,hft,hfn,hfr⟩ := canonicalTypedTerm n arity ctx.1.1 ctx.1.2 Gamma (.arrow sigma tau) x hF'
  obtain ⟨gt,hgt,hgn,hgr⟩ := canonicalTypedTerm n arity ctx.1.1 ctx.1.2 Gamma (.arrow sigma tau) y hG'
  obtain ⟨arg,hat,han,har⟩ := canonicalTypedTerm n arity ctx.1.1 ctx.1.2 Gamma sigma argument hA'
  have hcan : representativeCode ctx.1.1 ctx.1.2 ⟨sigma,arg⟩ =
      packedNumber (⟨sigma,arg⟩ : Packed (Fin n) arity Gamma) := har.trans han.symm
  have hpath' : positivePathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,ft⟩)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,gt⟩) certificate = true := by
    simpa only [hfr,hgr] using hpath
  have hout := ApplicationCertificateLiftPathCoreProof.actualPositiveLift n arity ctx hclosed Gamma
    sigma tau context hctx ft gt arg certificate hft hgt hat hcan hpath'
  have hfB := builderCalibration n arity ctx hclosed Gamma sigma tau context domain codomain
    f a x argument hctx hs ht hfo hao ft arg hft hat hfr har
  have hgB := builderCalibration n arity ctx hclosed Gamma sigma tau context domain codomain
    g a y argument hctx hs ht hgo hao gt arg hgt hat hgr har
  have hK : pathValue n arity (List.Vector.ofFn ![context,domain,codomain,a,certificate]) =
      liftPath n arity Gamma context (typeNumber sigma) (typeNumber tau)
        (packedNumber (⟨sigma,arg⟩ : Packed (Fin n) arity Gamma)) certificate := by
    simp [pathValue,hao,hsc,htc,han]
  rw [hfB,hgB,hK]
  simpa [ContextUniform.positiveValue,ContextUniform.objectCode,
    OrdinaryArithmeticQuotient.positiveValue,hctx] using hout

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathProof
