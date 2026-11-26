module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- Native correspondence to ORIGINAL capture-correct closed substitution,
including universalFunction syntax. No evaluation of that symbol. -/
def NativeSubstitution : Prop := ∀ (t : Term 1) (u : Term 0),
 evaluate (program t) (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
 Encodable.encode (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (fun _ => u) t))
/-- Genuine internal graph for every raw numeric input, including malformed
encodings. Literal constructor computation only, no validator/correctness premise. -/
def InternalGraph : Prop := ∀ (t : Term 1) n (p : Program n) (tag ctag atag : Nat),
 (nodes p)[tag]? = some ⟨1,program t⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (call tag (raw ::ᵥ nil)) (value ctag atag raw t)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.Targets
