module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- Native correspondence to the ORIGINAL allInstantiate axiom, closed substitution. -/
def NativeLine : Prop := ∀ (a b : Term 1) (u : Term 0),
 evaluate (line a b) (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
 Encodable.encode (nativeLine a b u)
/-- Original checker acceptance, not a new recognizer; well-formed closed argument only. -/
def NativeAcceptance : Prop := ∀ (a b : Term 1) (u : Term 0),
 HistoryDispatcher.logicalFunction (Encodable.encode (nativeLine a b u) ::ᵥ nil) = 1
/-- Literal constructor graph on every numeric raw input, without a validation premise.
Does not assert original checker acceptance on malformed arguments. -/
def InternalLine : Prop := ∀ (a b : Term 1) n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,line a b⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (call qtag (raw ::ᵥ nil)) (lineValue ptag ctag atag a b raw)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation.Targets
