module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetTestsPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecProof
open Source Source.SourceMarkedSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedAuxiliaryDecoding NumberedFiniteUniverse NumberedNumericDecoding NumberedNumericCarrier
open NumberedMultisetCertificate NumberedMultisetNumeric NumberedMulCertificate NumberedNumericMul
open NumberedMulPrimrec NumberedMulPrimrecSupportProof NumberedDirectCodePrimrecProof

attribute [local irreducible] Primrec argumentValues multisetTest mulCertificateTest
  decodePackedNumber decodeUniverse decodeCertificate

private abbrev BaseInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (Code (Fin n) × Code (Fin n)) × MultisetCertificate n arity Gamma

private def baseListTest (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (p : BaseInput n arity Gamma) : Bool :=
  (argumentValues n arity Gamma p.1.1).any (fun source =>
    (argumentValues n arity Gamma p.1.2).any (fun target => multisetTest source target p.2))

private theorem baseListTestPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (baseListTest n arity Gamma) := by
  let P := List (Packed (Fin n) arity Gamma)
  have htest : Primrec (fun p : (BaseInput n arity Gamma × P) × P =>
      multisetTest p.1.2 p.2 p.1.1.2) :=
    (NumberedMultisetTestsPrimrecProof.multisetTestPrimitive n arity Gamma).comp
      (g := fun p : (BaseInput n arity Gamma × P) × P => (p.1.2, p.2, p.1.1.2))
      ((Primrec.snd.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  have hright : Primrec (fun p : BaseInput n arity Gamma × P =>
      (argumentValues n arity Gamma p.1.1.2).any (fun target => multisetTest p.2 target p.1.2)) :=
    optionAnyPrimitive
      (f := fun p : BaseInput n arity Gamma × P => argumentValues n arity Gamma p.1.1.2)
      (g := fun (p : BaseInput n arity Gamma × P) (target : P) =>
        multisetTest p.2 target p.1.2)
      ((argumentValuesPrimitive n arity Gamma).comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) htest.to₂
  exact optionAnyPrimitive
    (f := fun p : BaseInput n arity Gamma => argumentValues n arity Gamma p.1.1)
    (g := fun (p : BaseInput n arity Gamma) (source : P) =>
      (argumentValues n arity Gamma p.1.2).any (fun target => multisetTest source target p.2))
    ((argumentValuesPrimitive n arity Gamma).comp (Primrec.fst.comp Primrec.fst)) hright.to₂

private abbrev PayloadInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  ((List (Fin n) × List Ty) × MultisetCertificate n arity Gamma) ×
    NumberedCodeAssemblyPrimrecProof.NumberedData n × (HeadCode (Fin n) × Code (Fin n))

private def payloadGuard (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (p : PayloadInput n arity Gamma) : Prop :=
  p.2.1.2.2.1 = headResult (decodeHead p.2.2.1) ∧
    RecursiveComparison.headEquivalent (decodeHead p.2.1.2.1) (decodeHead p.2.2.1) ∧
    HeadInWindow arity p.1.1.1 p.1.1.2 (decodeHead p.2.2.1)

private instance payloadGuardDecidable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (p : PayloadInput n arity Gamma) : Decidable (payloadGuard n arity Gamma p) := by
  unfold payloadGuard
  infer_instance

private theorem payloadGuardPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    PrimrecPred (payloadGuard n arity Gamma) := by
  have hsource : Primrec (fun p : PayloadInput n arity Gamma => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hf := Primrec.fst.comp hsource
  have htau := Primrec.fst.comp (Primrec.snd.comp hsource)
  have hg : Primrec (fun p : PayloadInput n arity Gamma => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht := Primrec.eq.comp htau
    ((NumberedHeadSignaturePrimrecProof.headResultPrimitive n).comp hg)
  have he := ((NumberedExchangeGuardsPrimrecProof.headEquivalencePrimitive n).comp
    (hf.pair hg)).primrecPred
  have hwindow : Primrec (fun p : PayloadInput n arity Gamma => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hw := ((NumberedHeadWindowPrimrecProof.headWindowPrimitive n arity).comp
    ((Primrec.fst.comp hwindow).pair ((Primrec.snd.comp hwindow).pair hg))).primrecPred
  exact ht.and (he.and hw)

private def payload (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (p : PayloadInput n arity Gamma) : Bool :=
  if p.2.1.1 = 0 then false else
    decide (payloadGuard n arity Gamma p) &&
      baseListTest n arity Gamma ((p.2.1.2.2.2.1, p.2.2.2), p.1.2)

private theorem payloadPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (payload n arity Gamma) := by
  have hsource : Primrec (fun p : PayloadInput n arity Gamma => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hbase : Primrec (fun p : PayloadInput n arity Gamma => p.2.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hsource)))
  have htarget : Primrec (fun p : PayloadInput n arity Gamma => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcertificate : Primrec (fun p : PayloadInput n arity Gamma => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hbaseTest : Primrec (fun p : PayloadInput n arity Gamma =>
      baseListTest n arity Gamma ((p.2.1.2.2.2.1, p.2.2.2), p.1.2)) :=
    (baseListTestPrimitive n arity Gamma).comp ((hbase.pair htarget).pair hcertificate)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hsource) (Primrec.const 0))
    (Primrec.const false)
    (Primrec.and.comp (payloadGuardPrimitive n arity Gamma).decide hbaseTest)

private abbrev CodeInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (List (Fin n) × List Ty) × Code (Fin n) × Code (Fin n) ×
    MultisetCertificate n arity Gamma

theorem mulCodePrimitive : NumberedMulPrimrecTargets.ActualMulCodePrimitive := by
  intro n arity Gamma
  let N := NumberedCodeAssemblyPrimrecProof.NumberedData n
  let O := HeadCode (Fin n) × Code (Fin n)
  have hdata : Primrec (fun p : (CodeInput n arity Gamma × N) × O => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hpayload : Primrec (fun p : (CodeInput n arity Gamma × N) × O =>
      payload n arity Gamma ((p.1.1.1, p.1.1.2.2.2), p.1.2, p.2)) :=
    (payloadPrimitive n arity Gamma).comp
      (((Primrec.fst.comp hdata).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hdata)))).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have htarget : Primrec (fun p : CodeInput n arity Gamma × N =>
      (ordinaryParts p.1.2.2.1).any (fun target =>
        payload n arity Gamma ((p.1.1, p.1.2.2.2), p.2, target))) :=
    optionAnyPrimitive
      (f := fun p : CodeInput n arity Gamma × N => ordinaryParts p.1.2.2.1)
      (g := fun (p : CodeInput n arity Gamma × N) (target : O) =>
        payload n arity Gamma ((p.1.1, p.1.2.2.2), p.2, target))
      ((ordinaryPartsPrimitive n).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) hpayload.to₂
  have hprogram : Primrec (fun p : CodeInput n arity Gamma =>
      (finiteNumberedParts p.2.1).any (fun source =>
        (ordinaryParts p.2.2.1).any (fun target =>
          payload n arity Gamma ((p.1, p.2.2.2), source, target)))) :=
    optionAnyPrimitive
      (f := fun p : CodeInput n arity Gamma => finiteNumberedParts p.2.1)
      (g := fun (p : CodeInput n arity Gamma) (source : N) =>
        (ordinaryParts p.2.2.1).any (fun target =>
          payload n arity Gamma ((p.1, p.2.2.2), source, target)))
      ((numberedPartsPrimitive n).comp (Primrec.fst.comp Primrec.snd)) htarget.to₂
  apply hprogram.of_eq
  rintro ⟨⟨symbols, S⟩, source, target, certificate⟩
  cases source with
  | var index => rfl
  | lam sigma body => rfl
  | app sigma f a => rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | argumentsNil => rfl
  | argumentsCons sigma q rest => rfl
  | numbered k f tau base types extras =>
    cases k with
    | zero => cases target <;> rfl
    | succ k =>
      cases target with
      | ordinary g targetBase =>
        cases hs : argumentValues n arity Gamma base <;>
          cases ht : argumentValues n arity Gamma targetBase <;>
          simp [finiteNumberedParts, ordinaryParts, payload, payloadGuard, baseListTest,
            codeMulTest, hs, ht]
      | var index => rfl
      | lam sigma body => rfl
      | app sigma q a => rfl
      | bottom rho => rfl
      | numbered label g rho targetBase otherTypes otherExtras => rfl
      | argumentsNil => rfl
      | argumentsCons sigma q rest => rfl

theorem mulCodeCalibration : NumberedMulPrimrecTargets.ActualMulCodeCalibration :=
  NumberedMulPrimrecSupportProof.mulCodeCalibration

theorem mulCertificatePrimitive : NumberedMulPrimrecTargets.ActualMulCertificatePrimitive := by
  intro n arity Gamma
  let Input := (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma ×
    Packed (Fin n) arity Gamma × MultisetCertificate n arity Gamma
  have hsource : Primrec (fun p : Input => termCode p.2.1.2) :=
    Primrec.snd.comp ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp
      (Primrec.fst.comp Primrec.snd))
  have htarget : Primrec (fun p : Input => termCode p.2.2.1.2) :=
    Primrec.snd.comp ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hinput : Primrec (fun p : Input =>
      (p.1, termCode p.2.1.2, termCode p.2.2.1.2, p.2.2.2)) :=
    Primrec.fst.pair (hsource.pair (htarget.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact ((mulCodePrimitive n arity Gamma).comp
    (g := fun p : Input => (p.1, termCode p.2.1.2, termCode p.2.2.1.2, p.2.2.2)) hinput).of_eq
    (fun p => mulCodeCalibration n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2)

theorem numericMulPrimitive : NumberedMulPrimrecTargets.ActualNumericMulPrimitive := by
  intro n arity Gamma
  let Input := (List (Fin n) × List Ty) × Nat × Nat × Nat
  let P := Packed (Fin n) arity Gamma
  let C := MultisetCertificate n arity Gamma
  have htargetNumber : Primrec (fun p : Input => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcertificateNumber : Primrec (fun p : Input => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hdata : Primrec (fun p : ((Input × P) × P) × C => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htest : Primrec (fun p : ((Input × P) × P) × C =>
      mulCertificateTest n arity p.1.1.1.1.1 p.1.1.1.1.2 Gamma p.1.1.2 p.1.2 p.2) :=
    (mulCertificatePrimitive n arity Gamma).comp
      ((Primrec.fst.comp hdata).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  have hcertificate : Primrec (fun p : (Input × P) × P =>
      (decodeCertificate n arity Gamma p.1.1.2.2.2).any (fun c =>
        mulCertificateTest n arity p.1.1.1.1 p.1.1.1.2 Gamma p.1.2 p.2 c)) :=
    optionAnyPrimitive
      (f := fun p : (Input × P) × P => decodeCertificate n arity Gamma p.1.1.2.2.2)
      (g := fun (p : (Input × P) × P) (c : C) =>
        mulCertificateTest n arity p.1.1.1.1 p.1.1.1.2 Gamma p.1.2 p.2 c)
      ((NumberedMultisetPresentationProof.decodeCertificatePrimitive n arity Gamma).comp
        (hcertificateNumber.comp (Primrec.fst.comp Primrec.fst))) htest.to₂
  have htarget : Primrec (fun p : Input × P =>
      (decodePackedNumber n arity Gamma p.1.2.2.1).any (fun r =>
        (decodeCertificate n arity Gamma p.1.2.2.2).any (fun c =>
          mulCertificateTest n arity p.1.1.1 p.1.1.2 Gamma p.2 r c))) :=
    optionAnyPrimitive
      (f := fun p : Input × P => decodePackedNumber n arity Gamma p.1.2.2.1)
      (g := fun (p : Input × P) (r : P) =>
        (decodeCertificate n arity Gamma p.1.2.2.2).any (fun c =>
          mulCertificateTest n arity p.1.1.1 p.1.1.2 Gamma p.2 r c))
      ((NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp
        (htargetNumber.comp Primrec.fst)) hcertificate.to₂
  have hsource : Primrec (fun p : Input =>
      decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.1) :=
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hprogram : Primrec (fun p : Input =>
      (decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.1).any (fun q =>
        (decodePackedNumber n arity Gamma p.2.2.1).any (fun r =>
          (decodeCertificate n arity Gamma p.2.2.2).any (fun c =>
            mulCertificateTest n arity p.1.1 p.1.2 Gamma q r c)))) :=
    optionAnyPrimitive
      (f := fun p : Input => decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.1)
      (g := fun (p : Input) (q : P) =>
        (decodePackedNumber n arity Gamma p.2.2.1).any (fun r =>
          (decodeCertificate n arity Gamma p.2.2.2).any (fun c =>
            mulCertificateTest n arity p.1.1 p.1.2 Gamma q r c))) hsource htarget.to₂
  apply hprogram.of_eq
  intro p
  cases hs : decodeUniverse n arity p.1.1 p.1.2 Gamma p.2.1 <;>
    cases ht : decodePackedNumber n arity Gamma p.2.2.1 <;>
    cases hc : decodeCertificate n arity Gamma p.2.2.2 <;>
    simp [numericMulTest, hs, ht, hc]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecProof
