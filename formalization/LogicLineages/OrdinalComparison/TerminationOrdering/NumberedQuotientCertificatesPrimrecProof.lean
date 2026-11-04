module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecProof
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericCarrier NumberedNumericStep NumberedNumericQuotientEdge NumberedQuotientPathCertificates
open NumberedQuotientPathPrimrecSupportProof

abbrev PayloadInput (n : Nat) := (Window n × Table n) × (Nat × Nat × Nat) × (Nat × Nat)

def payloadTest (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (p : PayloadInput n) : Bool :=
  (decodeUniverse n arity p.1.1.1 p.1.1.2 Gamma p.2.1.1).any (fun q =>
    (decodePackedNumber n arity Gamma p.2.1.2.1).any (fun r =>
      numericStepTest n arity p.1.1.1 p.1.1.2 Gamma p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2 &&
        decide (representativeCode p.1.1.1 p.1.1.2 q = p.2.2.1 ∧
          representativeCode p.1.1.1 p.1.1.2 r = p.2.2.2)))

attribute [local irreducible] Primrec representativeCode numericStepTest

theorem payloadPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (payloadTest n arity Gamma) := by
  have hparams : Primrec (fun p : (PayloadInput n × Packed (Fin n) arity Gamma) ×
      Packed (Fin n) arity Gamma => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw := Primrec.fst.comp (Primrec.fst.comp hparams)
  have ht := Primrec.snd.comp (Primrec.fst.comp hparams)
  have hc := Primrec.fst.comp (Primrec.snd.comp hparams)
  have he := Primrec.snd.comp (Primrec.snd.comp hparams)
  have hs := (NumberedNumericStepPrimrecProof.numericStepPrimitive n arity).comp
    (hw.pair (ht.pair ((Primrec.const Gamma).pair
      ((Primrec.fst.comp hc).pair ((Primrec.fst.comp (Primrec.snd.comp hc)).pair
        (Primrec.snd.comp (Primrec.snd.comp hc)))))))
  have hq := (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
    (hw.pair (Primrec.snd.comp Primrec.fst))
  have hr := (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
    (hw.pair Primrec.snd)
  have hcompare := ((Primrec.eq.comp hq (Primrec.fst.comp he)).and
    (Primrec.eq.comp hr (Primrec.snd.comp he))).decide
  have hbody : Primrec (fun p : (PayloadInput n × Packed (Fin n) arity Gamma) ×
      Packed (Fin n) arity Gamma =>
      numericStepTest n arity p.1.1.1.1.1 p.1.1.1.1.2 Gamma p.1.1.1.2
        p.1.1.2.1.1 p.1.1.2.1.2.1 p.1.1.2.1.2.2 &&
      decide (representativeCode p.1.1.1.1.1 p.1.1.1.1.2 p.1.2 = p.1.1.2.2.1 ∧
        representativeCode p.1.1.1.1.1 p.1.1.1.1.2 p.2 = p.1.1.2.2.2)) :=
    Primrec.and.comp hs hcompare
  have htarget : Primrec (fun p : PayloadInput n × Packed (Fin n) arity Gamma =>
      (decodePackedNumber n arity Gamma p.1.2.1.2.1).any (fun r =>
        numericStepTest n arity p.1.1.1.1 p.1.1.1.2 Gamma p.1.1.2
          p.1.2.1.1 p.1.2.1.2.1 p.1.2.1.2.2 &&
        decide (representativeCode p.1.1.1.1 p.1.1.1.2 p.2 = p.1.2.2.1 ∧
          representativeCode p.1.1.1.1 p.1.1.1.2 r = p.1.2.2.2))) :=
    optionAnyPrimitive
      ((NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))) hbody.to₂
  exact optionAnyPrimitive
    ((NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))) htarget.to₂

theorem numericEdgePrimitive :
    NumberedQuotientCertificatesPrimrecTargets.ActualNumericEdgePrimitive := by
  intro n arity Gamma
  have hc : Primrec (fun p : EdgeInput n => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hu := Primrec.unpair.comp hc
  have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hi : Primrec (fun p : EdgeInput n =>
      ((p.1,p.2.1),((Nat.unpair p.2.2.2.2).1,
        (Nat.unpair (Nat.unpair p.2.2.2.2).2).1,(Nat.unpair (Nat.unpair p.2.2.2.2).2).2),
        (p.2.2.1,p.2.2.2.1))) :=
    (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair
      (((Primrec.fst.comp hu).pair ((Primrec.fst.comp hv).pair (Primrec.snd.comp hv))).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  apply ((payloadPrimitive n arity Gamma).comp hi).of_eq
  intro p
  unfold payloadTest numericEdgeTest
  dsimp only
  cases decodeUniverse n arity p.1.1 p.1.2 Gamma (Nat.unpair p.2.2.2.2).1 <;>
    cases decodePackedNumber n arity Gamma (Nat.unpair (Nat.unpair p.2.2.2.2).2).1 <;> rfl

theorem pathCertificateDecoderPrimitive :
    NumberedQuotientCertificatesPrimrecTargets.ActualPathCertificateDecoderPrimitive :=
  NumberedQuotientPathPrimrecSupportProof.pathCertificateDecoderPrimitive

theorem pathTestPrimitive :
    NumberedQuotientCertificatesPrimrecTargets.ActualPathTestPrimitive := by
  intro n arity Gamma
  exact pathTestPrimitiveOfEdge n arity Gamma (numericEdgePrimitive n arity Gamma)

theorem positivePathTestPrimitive :
    NumberedQuotientCertificatesPrimrecTargets.ActualPositivePathTestPrimitive := by
  intro n arity Gamma
  exact positivePathTestPrimitiveOfPath n arity Gamma (pathTestPrimitive n arity Gamma)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecProof
