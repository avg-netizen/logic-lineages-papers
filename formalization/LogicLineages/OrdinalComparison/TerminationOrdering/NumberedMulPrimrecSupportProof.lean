module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCodePrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedMultisetCertificate NumberedMultisetNumeric NumberedMulCertificate
open NumberedMulPrimrec NumberedExchangeCode

attribute [local irreducible] Primrec decodePackedNumbers

theorem argumentValuesCalibration (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (args : AuxArguments (Fin n) arity Gamma types) :
    argumentValues n arity Gamma (argumentsCode args) = some (argumentList args) := by
  unfold argumentValues
  rw [NumberedExchangeCalibrationSupportProof.argumentEntriesCalibration]
  simp only [Option.bind_some, List.map_map]
  change decodePackedNumbers n arity Gamma ((argumentList args).map packedNumber) = _
  exact NumberedMultisetNumericSupportProof.packedNumbersRoundTrip n arity Gamma (argumentList args)

theorem argumentValuesPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (argumentValues n arity Gamma) := by
  have hentry : Primrec (fun entry : Ty × Code (Fin n) =>
      Nat.pair (typeNumber entry.1) (codeNumber entry.2)) :=
    Primrec₂.natPair.comp
      (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.fst)
      ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd)
  have hlist : Primrec (fun entries : List (Ty × Code (Fin n)) =>
      entries.map (fun entry => Nat.pair (typeNumber entry.1) (codeNumber entry.2))) :=
    Primrec.list_map Primrec.id (hentry.comp Primrec.snd).to₂
  have hdecode : Primrec (fun entries : List (Ty × Code (Fin n)) =>
      decodePackedNumbers n arity Gamma
        (entries.map (fun entry => Nat.pair (typeNumber entry.1) (codeNumber entry.2)))) :=
    (NumberedMultisetPresentationProof.decodePackedNumbersPrimitive n arity Gamma).comp
      (g := fun entries : List (Ty × Code (Fin n)) =>
        entries.map (fun entry => Nat.pair (typeNumber entry.1) (codeNumber entry.2))) hlist
  exact Primrec.option_bind
    (f := @argumentEntries (Fin n))
    (g := fun (_ : Code (Fin n)) (entries : List (Ty × Code (Fin n))) =>
      decodePackedNumbers n arity Gamma
        (entries.map (fun entry => Nat.pair (typeNumber entry.1) (codeNumber entry.2))))
    (NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n)
    (hdecode.comp Primrec.snd).to₂

theorem mulCodeCalibration : NumberedMulPrimrecTargets.ActualMulCodeCalibration := by
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
      cases r <;> simp [termCode, codeMulTest, mulCertificateTest,
        NumberedAuxiliaryDecodingProof.headRoundTrip, argumentValuesCalibration]

theorem optionAnyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → Option B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) :=
  (Primrec.option_casesOn hf (Primrec.const false) hg).of_eq
    (by intro a; cases f a <;> rfl)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecSupportProof
