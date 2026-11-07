module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProgramProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProof
open Source ApplicationDomain ApplicationResultBuilder NumberedLeastCodeRepresentative

theorem actualArrowCalibration : ApplicationDomainTargets.ActualArrowCalibration := by
  intro domain codomain
  obtain ⟨sigma,hs,hes⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal domain
  obtain ⟨tau,ht,het⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal codomain
  refine ⟨sigma,tau,hs,ht,?_⟩
  have he : typeNumber (.arrow sigma tau) = arrowCode domain codomain := by
    simp [typeNumber,arrowCode,hes,het,Nat.add_comm]
  rw [← he]
  exact NumberedNumericDecodingProof.typeNumericRoundTrip _

/-- Decoder uniqueness aligns the *actual* raw context with each typed test.
No assertion that this Context number is its canonical encoding is needed. -/
theorem typedFiberCheck (n : Nat) (arity : Fin n → Nat)
    (context typ object : Nat) (Gamma : List Ty) (value : Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (tau : Ty)
    (ho : Encodable.decode (α := ContextUniform.Object) object = some (Gamma,value))
    (hc : Encodable.decode context = some ctx)
    (ht : NumberedNumericDecoding.decodeType typ = some tau)
    (h : JointGammaTyped.typedValue n arity (List.Vector.ofFn ![context,typ,object]) = 1) :
    NumberedTypedCarrier.typedCanonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma tau value = true := by
  obtain ⟨Delta,x,hx,c,s,hc',hs,hv⟩ :=
    (JointGammaTypedProof.calibration n arity context typ object).mp h
  have he := Option.some.inj (hx.symm.trans ho)
  have hG := congrArg Prod.fst he
  have hV := congrArg Prod.snd he
  dsimp only at hG hV
  subst Delta
  subst x
  have hC := Option.some.inj (hc'.symm.trans hc)
  subst c
  have hT := Option.some.inj (hs.symm.trans ht)
  subst s
  exact hv

/-- Existence together with original output typing and original same-Gamma.
All context and type equations refer to the caller's original numeric inputs. -/
theorem domainWitness (n : Nat) (arity : Fin n → Nat)
    (context domain codomain f a : Nat)
    (h : active n arity (List.Vector.ofFn ![context,domain,codomain,f,a])) :
    ∃ z : Nat,
      JointGammaApplication.encodedApplication n arity context domain codomain f a z ∧
      JointGammaTyped.encodedTyped n arity context codomain z ∧
      JointGammaDomain.sameContext f z := by
  rcases h with ⟨hW,hF,hA,hG⟩
  obtain ⟨ctx,hctx,hclosed⟩ :=
    (GuardCalibrationProof.actualValidWindowCalibration n context).1.mp hW
  obtain ⟨sigma,tau,hs,ht,harr⟩ := actualArrowCalibration domain codomain
  obtain ⟨Gamma,x,y,hx,hy⟩ :=
    (JointGammaDomainProof.actualGuardCalibration.1 f a).mp hG
  have hf := typedFiberCheck n arity context (arrowCode domain codomain) f
    Gamma x ctx (.arrow sigma tau) hx hctx harr hF
  have ha := typedFiberCheck n arity context domain a Gamma y ctx sigma hy hctx hs hA
  obtain ⟨⟨fty,ft⟩,hft,hfty,hfr⟩ :=
    (NumberedTypedCarrierProof.typedCanonicalCarrier n arity ctx.1.1 ctx.1.2
      hclosed Gamma (.arrow sigma tau) x).mp hf
  obtain ⟨⟨aty,arg⟩,hat,haty,har⟩ :=
    (NumberedTypedCarrierProof.typedCanonicalCarrier n arity ctx.1.1 ctx.1.2
      hclosed Gamma sigma y).mp ha
  dsimp only at hfty haty
  subst fty
  subst aty
  have happ := NumberedNumericApplicationProof.canonicalApplicationCalibration n arity
    ctx.1.1 ctx.1.2 hclosed Gamma sigma tau ft arg hft hat
  rw [hfr,har] at happ
  let value := representativeCode ctx.1.1 ctx.1.2 (NumberedQuotientApplication.applicationPacked ft arg)
  have hdecoded : OrdinaryArithmeticApplication.decodedApplication n arity Gamma
      context domain codomain x y = some value := by
    simpa [OrdinaryArithmeticApplication.decodedApplication,hctx,hs,ht] using happ
  have htyped : NumberedTypedCarrier.typedCanonicalCarrierTest n arity ctx.1.1 ctx.1.2
      Gamma tau value = true := by
    obtain ⟨_,_,_,_,_,_,_,hv⟩ :=
      NumberedNumericApplicationProof.canonicalApplicationSound n arity ctx.1.1 ctx.1.2
        hclosed Gamma sigma tau x y value happ
    exact hv
  refine ⟨ContextUniform.objectCode Gamma value,?_,?_,?_⟩
  · exact ⟨Gamma,x,y,value,hx,hy,Encodable.encodek _,hdecoded⟩
  · exact ⟨Gamma,value,Encodable.encodek _,ctx,tau,hctx,ht,htyped⟩
  · exact ⟨Gamma,x,value,hx,Encodable.encodek _⟩

theorem actualDomainSuccess : ApplicationDomainTargets.ActualDomainSuccess := by
  intro n arity context domain codomain f a v h
  obtain ⟨z,hz,_,_⟩ := domainWitness n arity context domain codomain f a h
  have ho := (ApplicationResultBuilderProof.actualPartialCalibration n arity
    context domain codomain f a z).mpr hz
  have hs := (ApplicationResultBuilderProof.partialTotal n arity _ z).mp ho
  refine ⟨?_,hs.1,?_⟩
  · simpa only [hs.2] using ho
  · exact (ApplicationResultBuilderProof.actualTotalCalibration n arity
      context domain codomain f a _).mpr ⟨hs.1,rfl⟩

theorem actualDomainResultCalibration : ApplicationDomainTargets.ActualDomainResultCalibration := by
  intro n arity context domain codomain f a z v h
  have hs := (actualDomainSuccess n arity context domain codomain f a h).2.1
  rw [ApplicationResultBuilderProof.actualTotalCalibration]
  exact and_iff_right hs

theorem actualDomainResultTyped : ApplicationDomainTargets.ActualDomainResultTyped := by
  intro n arity context domain codomain f a v h
  obtain ⟨z,hz,ht,hg⟩ := domainWitness n arity context domain codomain f a h
  have ho := (ApplicationResultBuilderProof.actualPartialCalibration n arity
    context domain codomain f a z).mpr hz
  have he := ((ApplicationResultBuilderProof.partialTotal n arity _ z).mp ho).2
  rw [← he]
  exact ⟨(JointGammaTypedProof.calibration n arity context codomain z).mpr ht,
    (JointGammaDomainProof.actualGuardCalibration.1 f z).mpr hg⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProof
