module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsDecoderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDirectProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
open Source JointGammaProgramsDecoderProof JointGammaQuotient
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

theorem scalarPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (ContextUniform.scalarValue n arity) := by
  let f := fun p : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object =>
    ContextUniformPrimary.canonicalCarrier n arity p.1.1.1 p.1.1.2 p.2.1 p.2.2
  have hf : Primrec f := (ContextUniformPrimaryPrimitiveProof.actualUniformCanonicalPrimitive n arity).comp
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)))
  have he : f = fun p : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object =>
      NumberedNumericCarrier.canonicalCarrierTest n arity p.1.1.1 p.1.1.2 p.2.1 p.2.2 := by
    funext p
    exact ContextUniformPrimaryCalibrationProof.actualUniformCanonicalCalibration n arity p.1.1.1 p.1.1.2 p.2.1 p.2.2
  have h := decodedUnaryPrimitive n f hf
  rw [he] at h
  apply h.of_eq
  intro v
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0) <;>
    cases ho : Encodable.decode (α := ContextUniform.Object) (v.get 1) <;>
    simp only [ContextUniform.scalarValue,OrdinaryArithmeticCarrier.scalarValue,hc,ho,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Option.any_none,Option.any_some] <;> rfl

theorem listBodyPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object =>
      (Encodable.decode (α := List Nat) p.2.2).any (fun values =>
        values.all (ContextUniformPrimary.canonicalCarrier n arity p.1.1.1 p.1.1.2 p.2.1))) := by
  let Input := OrdinaryArithmeticQuotient.Context n × ContextUniform.Object
  have hd : Primrec (fun p : Input => Encodable.decode (α := List Nat) p.2.2) :=
    Primrec.decode.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun p : (Input × List Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp := (ContextUniformPrimaryPrimitiveProof.actualUniformCanonicalPrimitive n arity).comp
    ((Primrec.fst.comp (Primrec.fst.comp hbase)).pair
      ((Primrec.fst.comp (Primrec.snd.comp hbase)).pair Primrec.snd))
  have hall := OrdinaryArithmeticCarrierSupportProof.listAllPrimitive Primrec.snd hp.to₂
  exact (NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive hd hall.to₂).of_eq (by intro p; rfl)

theorem listPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (ContextUniform.listValue n arity) := by
  let f := fun p : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object =>
    (Encodable.decode (α := List Nat) p.2.2).any (fun values =>
      values.all (ContextUniformPrimary.canonicalCarrier n arity p.1.1.1 p.1.1.2 p.2.1))
  have he : f = fun p : OrdinaryArithmeticQuotient.Context n × ContextUniform.Object =>
      (Encodable.decode (α := List Nat) p.2.2).any
        (QuotientDirectCarrier.listCarrierTest n arity p.1.1.1 p.1.1.2 p.2.1) := by
    funext p
    have hcanon : ContextUniformPrimary.canonicalCarrier n arity p.1.1.1 p.1.1.2 p.2.1 =
        NumberedNumericCarrier.canonicalCarrierTest n arity p.1.1.1 p.1.1.2 p.2.1 := by
      funext value
      exact ContextUniformPrimaryCalibrationProof.actualUniformCanonicalCalibration n arity
        p.1.1.1 p.1.1.2 p.2.1 value
    simp only [f,hcanon]
    rfl
  have h := decodedUnaryPrimitive n f (listBodyPrimitive n arity)
  rw [he] at h
  apply h.of_eq
  intro v
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0) <;>
    cases ho : Encodable.decode (α := ContextUniform.Object) (v.get 1) <;>
    simp only [ContextUniform.listValue,OrdinaryArithmeticCarrier.listValue,hc,ho,
      List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Option.any_none,Option.any_some] <;> rfl

theorem positivePrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (ContextUniform.positiveValue n arity) := by
  let f := fun p : Parameters n × Nat × Nat × Nat =>
    NumberedQuotientPathCertificates.positivePathTest n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  have h := decodedBinaryPrimitive n f
    (JointGammaQuotientPathPrimitiveProof.actualJointPositivePrimitive n arity)
  apply h.of_eq
  intro v
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0) <;>
    cases hs : Encodable.decode (α := ContextUniform.Object) (v.get 1) <;>
      cases ht : Encodable.decode (α := ContextUniform.Object) (v.get 2)
  all_goals simp only [f,ContextUniform.positiveValue,OrdinaryArithmeticQuotient.positiveValue,hc,hs,ht,
    Option.any_none,Option.any_some,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (try split_ifs) <;>
    (try simp_all only [decide_true,decide_false,Bool.true_and,Bool.false_and]) <;> rfl

theorem directPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (ContextUniform.directValue n arity) := by
  let f := fun p : Parameters n × Nat × Nat × Nat =>
    QuotientDirectCertificates.numericTest n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  have h := decodedBinaryPrimitive n f (JointGammaDirectProof.actualJointNumericDirectPrimitive n arity)
  apply h.of_eq
  intro v
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0) <;>
    cases hs : Encodable.decode (α := ContextUniform.Object) (v.get 1) <;>
      cases ht : Encodable.decode (α := ContextUniform.Object) (v.get 2)
  all_goals simp only [f,ContextUniform.directValue,OrdinaryArithmeticDirect.directValue,hc,hs,ht,
    Option.any_none,Option.any_some,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals (try split_ifs) <;>
    (try simp_all only [decide_true,decide_false,Bool.true_and,Bool.false_and]) <;> rfl

theorem actualContextUniformPresentationExists : ContextUniformTargets.ActualContextUniformPresentationExists := by
  intro n arity
  obtain ⟨ps,hps⟩ := Proof.allPrimitiveFunctions 2 (ContextUniform.scalarValue n arity) (scalarPrimitive n arity)
  obtain ⟨pm,hpm⟩ := Proof.allPrimitiveFunctions 2 (ContextUniform.listValue n arity) (listPrimitive n arity)
  obtain ⟨pp,hpp⟩ := Proof.allPrimitiveFunctions 4 (ContextUniform.positiveValue n arity) (positivePrimitive n arity)
  obtain ⟨pd,hpd⟩ := Proof.allPrimitiveFunctions 4 (ContextUniform.directValue n arity) (directPrimitive n arity)
  exact ⟨⟨ps,pm,pp,pd⟩,hps,hpm,hpp,hpd⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsProof
