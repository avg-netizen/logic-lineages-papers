module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecProof
open Source NumberedRewriteReduction NumberedFinitePrimaryClass
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedRepresentativePrimrec

private abbrev Window (n : Nat) := List (Fin n) × List Ty
private abbrev Input (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  Window n × Packed (Fin n) arity Gamma

theorem representativeBound : NumberedRepresentativePrimrecTargets.ActualRepresentativeBound :=
  NumberedRepresentativePrimrecSupportProof.representativeBound

theorem boundedRepresentativeCalibration :
    NumberedRepresentativePrimrecTargets.ActualBoundedRepresentativeCalibration :=
  NumberedRepresentativePrimrecSupportProof.boundedRepresentativeCalibration

private theorem classNumberTestPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Input n arity Gamma × Nat =>
      classNumberTest p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hdecode : Primrec (fun p : Input n arity Gamma × Nat =>
      decodePackedNumber n arity Gamma p.2) :=
    (NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp Primrec.snd
  have htest : Primrec (fun p : (Input n arity Gamma × Nat) × Packed (Fin n) arity Gamma =>
      primaryTest p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2) :=
    (NumberedPrimaryClassPrimrecProof.primaryTestPrimitive n arity Gamma).comp
      (g := fun p : (Input n arity Gamma × Nat) × Packed (Fin n) arity Gamma =>
        (p.1.1.1, p.1.1.2, p.2))
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd))
  apply (Primrec.option_casesOn hdecode (Primrec.const false) htest.to₂).of_eq
  intro p
  unfold classNumberTest
  cases decodePackedNumber n arity Gamma p.2 <;> rfl

theorem representativePrimitive : NumberedRepresentativePrimrecTargets.ActualRepresentativePrimitive := by
  intro n arity Gamma
  have hbound : Primrec (fun p : Input n arity Gamma => packedNumber p.2 + 1) :=
    Primrec.succ.comp
      ((NumberedPackedCodecPrimrecProof.packedEncoderPrimitive n arity Gamma).comp Primrec.snd)
  have hrange : Primrec (fun p : Input n arity Gamma => List.range (packedNumber p.2 + 1)) :=
    Primrec.list_range.comp hbound
  apply (Primrec.list_findIdx hrange (classNumberTestPrimitive n arity Gamma).to₂).of_eq
  intro p
  exact boundedRepresentativeCalibration n arity Gamma p.1.1 p.1.2 p.2

theorem canonicalCarrierPrimitive : NumberedRepresentativePrimrecTargets.ActualCanonicalCarrierPrimitive := by
  intro n arity Gamma
  have hrep : Primrec (fun p : (Window n × Nat) × Packed (Fin n) arity Gamma =>
      representativeCode p.1.1.1 p.1.1.2 p.2) :=
    (representativePrimitive n arity Gamma).comp
      (g := fun p : (Window n × Nat) × Packed (Fin n) arity Gamma => (p.1.1, p.2))
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hcheck : Primrec (fun p : (Window n × Nat) × Packed (Fin n) arity Gamma =>
      decide (representativeCode p.1.1.1 p.1.1.2 p.2 = p.1.2)) :=
    (Primrec.eq.comp hrep (Primrec.snd.comp Primrec.fst)).decide
  apply (Primrec.option_casesOn
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma)
    (Primrec.const false) hcheck.to₂).of_eq
  intro p
  unfold canonicalCarrierTest
  cases decodeUniverse n arity p.1.1 p.1.2 Gamma p.2 <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecProof
