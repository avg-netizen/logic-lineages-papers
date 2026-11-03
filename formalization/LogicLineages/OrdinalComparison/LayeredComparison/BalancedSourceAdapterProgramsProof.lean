module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterDataProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCodeProgramsProof
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Proof
open BalancedEvaluation
open Program

attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode upperData certificateData
  upperAtoms coefficients headCodes originalConstant outsideCoefficients factors normOffset
  coefficientMass outsideMaximum multiplierMaximum offsetMaximum normMaximum threshold
  lowerCertificate BalancedAffineCode.lowerPart BalancedAffineCode.completeInput
  BalancedLargeGuardsCode.largeCode

private theorem affineLowerPart_primitive :
    Primrec (fun p : Nat × List Nat × Nat × Nat =>
      BalancedAffineCode.lowerPart p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  BalancedAffineCode.Proof.uniformPrimitiveRecursive.2.2.2.2.1

private theorem affineCompleteInput_primitive :
    Primrec (fun p : Nat × List Nat × Nat × Nat =>
      BalancedAffineCode.completeInput p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  BalancedAffineCode.Proof.uniformPrimitiveRecursive.2.2.2.2.2

private theorem largeCode_primitive :
    Primrec (fun p : Nat × List Nat × List Int × Int =>
      BalancedLargeGuardsCode.largeCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  BalancedLargeGuardsCode.Proof.uniformPrimitiveRecursive.2.2.2.2.2.2.2.2.2

private theorem termCodes_primitive :
    Primrec (fun p : Nat × List Nat × Nat × Nat × Nat =>
      termCodes p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let D := Nat × List Nat × Nat × Nat × Nat
  have hk : Primrec (fun p : D => p.1) := Primrec.fst
  have hshape : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : D => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hf : Primrec (fun p : D => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec (fun p : D => upperAtoms p.2.2.2.1 p.2.2.2.2) :=
    upperAtoms_primitive.comp he hf
  have hinputTail : Primrec (fun p : D × AtomData =>
      (p.1.2.2.1,Encodable.encode p.2)) :=
    (hc.comp Primrec.fst).pair (Primrec.encode.comp Primrec.snd)
  have hinputBody : Primrec (fun p : D × AtomData =>
      (p.1.2.1,p.1.2.2.1,Encodable.encode p.2)) :=
    (hshape.comp Primrec.fst).pair hinputTail
  have hinputArgs : Primrec (fun p : D × AtomData =>
      (p.1.1,p.1.2.1,p.1.2.2.1,Encodable.encode p.2)) :=
    (hk.comp Primrec.fst).pair hinputBody
  have hinputs : Primrec (fun p : D =>
      (upperAtoms p.2.2.2.1 p.2.2.2.2).map (fun a =>
        BalancedAffineCode.completeInput p.1 p.2.1 p.2.2.1 (Encodable.encode a))) :=
    Primrec.list_map ha (affineCompleteInput_primitive.comp hinputArgs).to₂
  have hleftArgs : Primrec (fun p : D => (p.1,p.2.1,p.2.2.1,p.2.2.2.1)) :=
    hk.pair (hshape.pair (hc.pair he))
  have hrightArgs : Primrec (fun p : D => (p.1,p.2.1,p.2.2.1,p.2.2.2.2)) :=
    hk.pair (hshape.pair (hc.pair hf))
  have hleft : Primrec (fun p : D =>
      BalancedAffineCode.lowerPart p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
    affineLowerPart_primitive.comp hleftArgs
  have hright : Primrec (fun p : D =>
      BalancedAffineCode.lowerPart p.1 p.2.1 p.2.2.1 p.2.2.2.2) :=
    affineLowerPart_primitive.comp hrightArgs
  exact Primrec.list_append.comp hinputs
    (Primrec.list_cons.comp hleft (Primrec.list_cons.comp hright (Primrec.const [])))

attribute [local irreducible] termCodes

private theorem formulaCode_primitive :
    Primrec (fun p : Nat × Nat × Nat × Int => formulaCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := Nat × Nat × Nat × Int
  have hk : Primrec (fun p : D => p.1) := Primrec.fst
  have he : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : D => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hthresholdArgs : Primrec (fun p : D => (p.1,p.2.1,p.2.2.1)) :=
    hk.pair (he.pair hf)
  have hthreshold : Primrec (fun p : D => threshold p.1 p.2.1 p.2.2.1) :=
    threshold_primitive.comp hthresholdArgs
  have hheads : Primrec (fun p : D => headCodes p.2.1 p.2.2.1) :=
    headCodes_primitive.comp he hf
  have hcoefficients : Primrec (fun p : D => coefficients p.2.1 p.2.2.1) :=
    coefficients_primitive.comp he hf
  have htail : Primrec (fun p : D => (coefficients p.2.1 p.2.2.1,p.2.2.2)) :=
    hcoefficients.pair hd
  have hbody : Primrec (fun p : D =>
      (headCodes p.2.1 p.2.2.1,coefficients p.2.1 p.2.2.1,p.2.2.2)) :=
    hheads.pair htail
  have hargs : Primrec (fun p : D =>
      (threshold p.1 p.2.1 p.2.2.1,headCodes p.2.1 p.2.2.1,
        coefficients p.2.1 p.2.2.1,p.2.2.2)) :=
    hthreshold.pair hbody
  exact largeCode_primitive.comp hargs

attribute [local irreducible] formulaCode

private theorem assemble_primitive :
    Primrec (fun p : Nat × List Nat × Nat × Nat × Nat × Int =>
      assemble p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let D := Nat × List Nat × Nat × Nat × Nat × Int
  have hk : Primrec (fun p : D => p.1) := Primrec.fst
  have hshape : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun p : D => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hf : Primrec (fun p : D => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hd : Primrec (fun p : D => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htermsTail : Primrec (fun p : D => (p.2.2.1,p.2.2.2.1,p.2.2.2.2.1)) :=
    hc.pair (he.pair hf)
  have htermsArgs : Primrec (fun p : D => (p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1)) :=
    hk.pair (hshape.pair htermsTail)
  have hterms : Primrec (fun p : D =>
      termCodes p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) :=
    termCodes_primitive.comp htermsArgs
  have hformulaTail : Primrec (fun p : D => (p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)) :=
    he.pair (hf.pair hd)
  have hformulaArgs : Primrec (fun p : D => (p.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)) :=
    hk.pair hformulaTail
  have hformula : Primrec (fun p : D =>
      formulaCode p.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
    formulaCode_primitive.comp hformulaArgs
  exact (lowerCertificate_primitive.comp hc).pair (hterms.pair hformula)

attribute [local irreducible] assemble

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨upperAtoms_primitive, coefficients_primitive, headCodes_primitive,
    originalConstant_primitive, outsideCoefficients_primitive, factors_primitive,
    normOffset_primitive, coefficientMass_primitive, outsideMaximum_primitive,
    multiplierMaximum_primitive, offsetMaximum_primitive, normMaximum_primitive,
    threshold_primitive, lowerCertificate_primitive, termCodes_primitive,
    formulaCode_primitive, assemble_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Proof
