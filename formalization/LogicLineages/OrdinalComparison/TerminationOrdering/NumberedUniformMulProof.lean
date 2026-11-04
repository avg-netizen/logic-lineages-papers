module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCodePrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulProof
open Source Source.SourceMarkedSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedAuxiliaryDecoding NumberedFiniteUniverse NumberedMultisetCertificate
open NumberedMultisetNumeric NumberedMulCertificate NumberedExchangeCode
open NumberedUniformPackedDecoding NumberedUniformMultiset NumberedUniformMul
open NumberedDirectCodePrimrecProof
open NumberedMulPrimrecSupportProof (optionAnyPrimitive)

attribute [local irreducible] Primrec rawMultisetTest decodeRawCertificate

theorem rawMulCalibration : NumberedUniformMulTargets.ActualRawMulCalibration := by
  intro n arity symbols S Gamma q r certificate
  rcases q with ⟨tau, q⟩
  rcases r with ⟨rho, r⟩
  cases q with
  | var v => rfl
  | lam body => rfl
  | app f a => rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | numbered k f tau base types extras =>
    cases k with
    | zero => cases r <;> rfl
    | succ k =>
      cases r with
      | var v => rfl
      | lam body => rfl
      | app q a => rfl
      | bottom rho => rfl
      | numbered label g rho targetTypes targetBase targetExtras => rfl
      | ordinary g target =>
        simp only [termCode, rawMulTest, mulCertificateTest,
          NumberedAuxiliaryDecodingProof.headRoundTrip,
          NumberedExchangeCalibrationSupportProof.argumentEntriesCalibration]
        rw [NumberedUniformMultisetProof.multisetCalibration n arity Gamma
          (argumentList base) (argumentList target) certificate]

private abbrev BaseInput (n : Nat) :=
  (Code (Fin n) × Code (Fin n)) × RawCertificate n

private def baseListTest (n : Nat) (p : BaseInput n) : Bool :=
  (argumentEntries p.1.1).any (fun source =>
    (argumentEntries p.1.2).any (fun target => rawMultisetTest source target p.2))

private theorem baseListTestPrimitive (n : Nat) : Primrec (baseListTest n) := by
  let P := List (RawPacked n)
  have htest : Primrec (fun p : (BaseInput n × P) × P =>
      rawMultisetTest p.1.2 p.2 p.1.1.2) :=
    (NumberedUniformMultisetProof.rawMultisetPrimitive n).comp
      (g := fun p : (BaseInput n × P) × P => (p.1.2, p.2, p.1.1.2))
      ((Primrec.snd.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  have hright : Primrec (fun p : BaseInput n × P =>
      (argumentEntries p.1.1.2).any (fun target => rawMultisetTest p.2 target p.1.2)) :=
    optionAnyPrimitive
      (f := fun p : BaseInput n × P => argumentEntries p.1.1.2)
      (g := fun (p : BaseInput n × P) (target : P) => rawMultisetTest p.2 target p.1.2)
      ((NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n).comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) htest.to₂
  exact optionAnyPrimitive
    (f := fun p : BaseInput n => argumentEntries p.1.1)
    (g := fun (p : BaseInput n) (source : P) =>
      (argumentEntries p.1.2).any (fun target => rawMultisetTest source target p.2))
    ((NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n).comp
      (Primrec.fst.comp Primrec.fst)) hright.to₂

private abbrev PayloadInput (n : Nat) :=
  ((List (Fin n) × List Ty) × RawCertificate n) ×
    NumberedCodeAssemblyPrimrecProof.NumberedData n × (HeadCode (Fin n) × Code (Fin n))

private def payloadGuard (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) : Prop :=
  p.2.1.2.2.1 = headResult (decodeHead p.2.2.1) ∧
    RecursiveComparison.headEquivalent (decodeHead p.2.1.2.1) (decodeHead p.2.2.1) ∧
    HeadInWindow arity p.1.1.1 p.1.1.2 (decodeHead p.2.2.1)

private instance payloadGuardDecidable (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) :
    Decidable (payloadGuard n arity p) := by
  unfold payloadGuard
  infer_instance

private theorem payloadGuardPrimitive (n : Nat) (arity : Fin n → Nat) :
    PrimrecPred (payloadGuard n arity) := by
  have hsource : Primrec (fun p : PayloadInput n => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hf := Primrec.fst.comp hsource
  have htau := Primrec.fst.comp (Primrec.snd.comp hsource)
  have hg : Primrec (fun p : PayloadInput n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht := Primrec.eq.comp htau
    ((NumberedHeadSignaturePrimrecProof.headResultPrimitive n).comp hg)
  have he := ((NumberedExchangeGuardsPrimrecProof.headEquivalencePrimitive n).comp
    (hf.pair hg)).primrecPred
  have hwindow : Primrec (fun p : PayloadInput n => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw := ((NumberedHeadWindowPrimrecProof.headWindowPrimitive n arity).comp
    ((Primrec.fst.comp hwindow).pair ((Primrec.snd.comp hwindow).pair hg))).primrecPred
  exact ht.and (he.and hw)

private def payload (n : Nat) (arity : Fin n → Nat) (p : PayloadInput n) : Bool :=
  if p.2.1.1 = 0 then false else
    decide (payloadGuard n arity p) && baseListTest n ((p.2.1.2.2.2.1, p.2.2.2), p.1.2)

private theorem payloadPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (payload n arity) := by
  have hsource : Primrec (fun p : PayloadInput n => p.2.1) := Primrec.fst.comp Primrec.snd
  have hbase : Primrec (fun p : PayloadInput n => p.2.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hsource)))
  have htarget : Primrec (fun p : PayloadInput n => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcertificate : Primrec (fun p : PayloadInput n => p.1.2) := Primrec.snd.comp Primrec.fst
  have hbaseTest : Primrec (fun p : PayloadInput n =>
      baseListTest n ((p.2.1.2.2.2.1, p.2.2.2), p.1.2)) :=
    (baseListTestPrimitive n).comp ((hbase.pair htarget).pair hcertificate)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hsource) (Primrec.const 0))
    (Primrec.const false) (Primrec.and.comp (payloadGuardPrimitive n arity).decide hbaseTest)

private abbrev CodeInput (n : Nat) :=
  (List (Fin n) × List Ty) × Code (Fin n) × Code (Fin n) × RawCertificate n

theorem rawMulPrimitive : NumberedUniformMulTargets.ActualRawMulPrimitive := by
  intro n arity
  let N := NumberedCodeAssemblyPrimrecProof.NumberedData n
  let O := HeadCode (Fin n) × Code (Fin n)
  have hdata : Primrec (fun p : (CodeInput n × N) × O => p.1.1) := Primrec.fst.comp Primrec.fst
  have hpayload : Primrec (fun p : (CodeInput n × N) × O =>
      payload n arity ((p.1.1.1, p.1.1.2.2.2), p.1.2, p.2)) :=
    (payloadPrimitive n arity).comp
      (((Primrec.fst.comp hdata).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hdata)))).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have htarget : Primrec (fun p : CodeInput n × N =>
      (ordinaryParts p.1.2.2.1).any (fun target =>
        payload n arity ((p.1.1, p.1.2.2.2), p.2, target))) :=
    optionAnyPrimitive
      (f := fun p : CodeInput n × N => ordinaryParts p.1.2.2.1)
      (g := fun (p : CodeInput n × N) (target : O) =>
        payload n arity ((p.1.1, p.1.2.2.2), p.2, target))
      ((ordinaryPartsPrimitive n).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) hpayload.to₂
  have hprogram : Primrec (fun p : CodeInput n =>
      (finiteNumberedParts p.2.1).any (fun source =>
        (ordinaryParts p.2.2.1).any (fun target => payload n arity ((p.1, p.2.2.2), source, target)))) :=
    optionAnyPrimitive
      (f := fun p : CodeInput n => finiteNumberedParts p.2.1)
      (g := fun (p : CodeInput n) (source : N) =>
        (ordinaryParts p.2.2.1).any (fun target => payload n arity ((p.1, p.2.2.2), source, target)))
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
        cases hs : argumentEntries base <;> cases ht : argumentEntries targetBase <;>
          simp [finiteNumberedParts, ordinaryParts, payload, payloadGuard, baseListTest,
            rawMulTest, hs, ht]
      | var index => rfl
      | lam sigma body => rfl
      | app sigma q a => rfl
      | bottom rho => rfl
      | numbered label g rho targetBase otherTypes otherExtras => rfl
      | argumentsNil => rfl
      | argumentsCons sigma q rest => rfl

theorem mulTestCalibration : NumberedUniformMulTargets.ActualMulTestCalibration := by
  intro n arity symbols S Gamma q r certificate
  unfold mulTest
  rw [NumberedUniformMultisetProof.certificateDecoderCalibration n arity Gamma certificate]
  cases decodeCertificate n arity Gamma certificate with
  | none => rfl
  | some data =>
    change rawMulTest arity symbols S (termCode q.2) (termCode r.2) (certificateData data) =
      mulCertificateTest n arity symbols S Gamma q r data
    exact rawMulCalibration n arity symbols S Gamma q r data

theorem mulTestPrimitive : NumberedUniformMulTargets.ActualMulTestPrimitive := by
  intro n arity
  let Input := (List (Fin n) × List Ty) × List Ty × Code (Fin n) × Code (Fin n) × Nat
  have hcertificate : Primrec (fun p : Input =>
      decodeRawCertificate n arity p.2.1 p.2.2.2.2) :=
    (NumberedUniformMultisetProof.certificateDecoderPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hsource : Primrec (fun p : Input × RawCertificate n => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have htarget : Primrec (fun p : Input × RawCertificate n => p.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have htest : Primrec (fun p : Input × RawCertificate n =>
      rawMulTest arity p.1.1.1 p.1.1.2 p.1.2.2.1 p.1.2.2.2.1 p.2) :=
    (rawMulPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair (hsource.pair (htarget.pair Primrec.snd)))
  exact optionAnyPrimitive
    (f := fun p : Input => decodeRawCertificate n arity p.2.1 p.2.2.2.2)
    (g := fun (p : Input) (certificate : RawCertificate n) =>
      rawMulTest arity p.1.1 p.1.2 p.2.2.1 p.2.2.2.1 certificate) hcertificate htest.to₂

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulProof
