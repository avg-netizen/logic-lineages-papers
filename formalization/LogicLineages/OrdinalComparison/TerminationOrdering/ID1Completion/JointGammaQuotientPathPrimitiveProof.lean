module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientEdgePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientPathPrimitiveProof
open Source NumberedNumericQuotientEdge NumberedQuotientPathCertificates JointGammaQuotient
open NumberedQuotientPathPrimrecSupportProof

attribute [local irreducible] Primrec numericEdgeTest pathTest

/-- Fold the ORIGINAL edge checker and retain the original terminal endpoint test. -/
theorem actualJointPathPrimitive : JointGammaQuotientTargets.ActualJointPathPrimitive := by
  intro n arity
  let Input := Parameters n × Nat × Nat × List EdgeEntry
  have he : Primrec (fun p : Input × ((Nat × Bool) × EdgeEntry) =>
      numericEdgeTest n arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2
        p.2.1.1 p.2.2.1 p.2.2.2) :=
    (JointGammaQuotientEdgePrimitiveProof.actualJointEdgePrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hs : Primrec (fun p : Input × ((Nat × Bool) × EdgeEntry) =>
      foldStep arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.2.1 p.2.2) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) he)
  have hf : Primrec (fun p : Input =>
      p.2.2.2.foldl (foldStep arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2) (p.2.1,true)) :=
    Primrec.list_foldl (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.const true)) hs.to₂
  have hfinish : Primrec (fun p : Input =>
      finish p.2.2.1
        (p.2.2.2.foldl (foldStep arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2) (p.2.1,true))) :=
    Primrec.and.comp (Primrec.snd.comp hf)
      (Primrec.eq.comp (Primrec.fst.comp hf) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).decide
  exact hfinish.of_eq (by
    intro p
    simpa only [Bool.true_and] using foldCalibration n arity p.1.1.1.1 p.1.1.1.2
      p.1.1.2 p.1.2 p.2.2.2 p.2.1 p.2.2.1 true)

/-- Use the ORIGINAL path certificate decoder, rejecting malformed and empty data. -/
theorem actualJointPositivePrimitive : JointGammaQuotientTargets.ActualJointPositivePrimitive := by
  intro n arity
  let Input := Parameters n × Nat × Nat × Nat
  have hp : Primrec (fun p : Input × List EdgeEntry =>
      pathTest n arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2
        p.1.2.1 p.1.2.2.1 p.2) :=
    (actualJointPathPrimitive n arity).comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)))
  have hb : Primrec (fun p : Input × List EdgeEntry =>
      decide (p.2 ≠ []) && pathTest n arity
        p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.1.2 p.1.2.1 p.1.2.2.1 p.2) :=
    Primrec.and.comp (Primrec.eq.comp Primrec.snd (Primrec.const [])).not.decide hp
  have hd : Primrec (fun p : Input => decodePathCertificate p.2.2.2) :=
    pathCertificateDecoderPrimitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h := optionAnyPrimitive hd hb.to₂
  apply h.of_eq
  intro p
  cases hc : decodePathCertificate p.2.2.2 with
  | none => simp only [positivePathTest,hc,Option.any_none]
  | some entries => cases entries <;> simp [positivePathTest,hc]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientPathPrimitiveProof
