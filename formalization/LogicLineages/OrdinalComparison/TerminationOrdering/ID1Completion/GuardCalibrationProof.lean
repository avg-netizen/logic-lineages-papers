module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeSubexpressionsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
open Source GuardCalibration NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

theorem actualTypeTagPrimitive : GuardCalibrationTargets.ActualTypeTagPrimitive := by
  have hg : Primrec (fun v : List.Vector Nat 2 => v.get 1) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const (1 : Fin 2))
  exact Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp hg)))

theorem actualTypeTagProgram : GuardCalibrationTargets.ActualTypeTagProgram :=
  Proof.allPrimitiveFunctions 2 typeTagValue actualTypeTagPrimitive

/-- Decode-filter soundness, not a closure theorem. In particular no claim
about an internal proof of decoder correctness occurs here. -/
theorem actualTypedTypeTag : GuardCalibrationTargets.ActualTypedTypeTag := by
  intro n arity context typ object h
  obtain ⟨Gamma,value,ho,ctx,tau,_hctx,ht,hval⟩ :=
    (JointGammaTypedProof.calibration n arity context typ object).mp h
  have heo : ContextUniform.objectCode Gamma value = object :=
    (JointGammaDomainCodecProof.actualObjectCodec.2.1 object (Gamma,value)).mp ho
  have hv : ∃ q : NumberedRewriteReduction.Packed (Fin n) arity Gamma,
      NumberedNumericCarrier.decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma value = some q ∧
      q.1 = tau ∧ representativeCode ctx.1.1 ctx.1.2 q = value := by
    simpa only [NumberedTypedCarrier.typedCanonicalCarrierTest,
      OrdinaryArithmeticCarrierSupportProof.optionAnyTrue,decide_eq_true_eq] using hval
  obtain ⟨q,hq,hqt,_hrep⟩ := hv
  have hvcode :=
    ((NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma value q).mp hq).1
  have htcode : typeNumber tau = typ := by
    simp only [NumberedNumericDecoding.decodeType,Option.filter_eq_some_iff,decide_eq_true_eq] at ht
    exact ht.2
  calc
    typeTag context object = (Nat.unpair value).1 := by
      rw [← heo]
      simp only [typeTag,ContextUniform.objectCode,Encodable.encode_prod_val,
        Encodable.encode_nat,Nat.unpair_pair]
    _ = typeNumber q.1 := by
      rw [← hvcode]
      simp only [packedNumber,Nat.unpair_pair]
    _ = typ := by rw [hqt]; exact htcode

theorem actualSubtypeClosedCalibration : GuardCalibrationTargets.ActualSubtypeClosedCalibration := by
  intro S
  simp only [subtypeClosedTest,List.all_eq_true,decide_eq_true_eq,SubtypeClosed]

theorem subtypeClosedTestPrimitive : Primrec subtypeClosedTest := by
  have hsub : PrimrecRel (fun (sigma : Ty) (S : List Ty) => ∀ tau ∈ sigma.subtypes, tau ∈ S) :=
    (NumberedHeadWindowPrimrecProof.membersPrimitive Ty).comp
      (NumberedTypeSubexpressionsPrimrecProof.typeSubexpressionsPrimitive.comp Primrec.fst) Primrec.snd
  have hc : PrimrecPred (fun S : List Ty => ∀ sigma ∈ S, ∀ tau ∈ sigma.subtypes, tau ∈ S) :=
    hsub.forall_mem_list.comp Primrec.id Primrec.id
  apply hc.decide.of_eq
  intro S
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,subtypeClosedTest,List.all_eq_true]

theorem validWindowPrimitive (n : Nat) : Primrec (validWindow n) := by
  have hb : Primrec (fun p : Nat × OrdinaryArithmeticQuotient.Context n =>
      subtypeClosedTest p.2.1.2) :=
    subtypeClosedTestPrimitive.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  exact (Primrec.dom_bool Bool.toNat).comp
    (NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive
      (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n) hb.to₂)

theorem actualValidWindowPrimitive : GuardCalibrationTargets.ActualValidWindowPrimitive := by
  intro n
  exact (validWindowPrimitive n).comp
    (Primrec.vector_get.comp Primrec.id (Primrec.const (0 : Fin 1)))

theorem actualValidWindowCalibration : GuardCalibrationTargets.ActualValidWindowCalibration := by
  intro n context
  have hone : validWindow n context = 1 ↔
      ∃ ctx : OrdinaryArithmeticQuotient.Context n,
        Encodable.decode context = some ctx ∧ SubtypeClosed (fun tau => tau ∈ ctx.1.2) := by
    simp only [validWindow,Bool.toNat_eq_one,
      OrdinaryArithmeticCarrierSupportProof.optionAnyTrue]
    apply exists_congr
    intro ctx
    exact and_congr_right (fun _ => actualSubtypeClosedCalibration ctx.1.2)
  have hzero : validWindow n context = 0 ↔ ¬ validWindow n context = 1 := by
    unfold validWindow
    cases (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) context).any
      (fun ctx => subtypeClosedTest ctx.1.2) <;> simp
  exact ⟨hone,hzero.trans (not_congr hone)⟩

theorem actualOriginalWindowCalibration : GuardCalibrationTargets.ActualOriginalWindowCalibration := by
  intro n symbols S table
  simp only [validWindow,OrdinaryArithmeticQuotient.contextCode,Encodable.encodek,
    Option.any_some,Bool.toNat_eq_one]
  exact actualSubtypeClosedCalibration S

theorem actualValidWindowProgram : GuardCalibrationTargets.ActualValidWindowProgram := by
  intro n
  exact Proof.allPrimitiveFunctions 1 (validWindowValue n) (actualValidWindowPrimitive n)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
