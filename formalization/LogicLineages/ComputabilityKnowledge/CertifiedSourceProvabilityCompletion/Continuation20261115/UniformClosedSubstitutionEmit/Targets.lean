module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- Original shiftRaw identity must be paid; no native-image assumption. -/
def ClosedShiftIdentity : Prop := ∀ b (raw : List Nat),
 GorbowSyntaxValidation.validTerm 0 raw = true → GorbowTermShiftCode.shiftRaw 0 b raw = raw
/-- All original States/tokens, including NONE, SOME[], invalid task kinds and
context0. Closed replacement validity is explicit and indispensable. -/
def ExactOriginalEmit : Prop := ∀ (s : GorbowSyntaxValidation.State) (token : Nat) (raw : List Nat),
 GorbowSyntaxValidation.validTerm 0 raw = true →
 evaluate emitCode (Encodable.encode s ::ᵥ token ::ᵥ Encodable.encode raw ::ᵥ nil) =
 Encodable.encode (GorbowSubstitutionCode.emit 1 0 [raw] s token)
/-- Actual graph branch laws on arbitrary runtime terms. No native calibration
or valid-code hypothesis is used internally. The two invalid-bound0 branches
are explicit; successor-bound laws pay the real binder boundary arithmetic. -/
def InternalBranches : Prop := ∀ n (p : Program n) (etag ptag ctag : Nat),
 (nodes p)[etag]? = some ⟨3,emitCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (token raw kind bound rest depth gap : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag .zero token raw) (singletonValue ctag token))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (.succ .zero) token raw) (singletonValue ctag token))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag .zero bound rest) .zero raw) .zero)) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag .zero bound rest) (.succ token) raw)
   (singletonValue ctag (.succ token)))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.neg (.equal kind .zero)) (.imp (.neg (.equal kind (Term.numeral 2)))
   (.equal (emitCall etag (stateValue ptag ctag kind bound rest) token raw) (singletonValue ctag token))))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (.add token (.succ gap)) depth)
   (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) token raw)
    (variableValue ctag token)))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) depth raw) raw)) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (.add depth (.succ gap)) token)
   (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) token raw) .zero))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2) .zero rest) .zero raw) raw)) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2) .zero rest) (.succ token) raw) .zero))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.Targets
