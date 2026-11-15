module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- All raw token lists, including malformed syntax and invalid replacements;
no Formula/Term AST image premise. Literal original Option(List Nat) codec. -/
def ExactOriginalInstance : Prop := ∀ (formula replacement : List Nat),
 evaluate instanceCode (Encodable.encode formula ::ᵥ Encodable.encode replacement ::ᵥ nil) =
 Encodable.encode (GorbowInstanceCode.instanceCode 0 formula replacement)
/-- Total internal guarded graph on arbitrary terms: original guards imply
Some(actual output), and their negation implies None. No external success or
validation assumption, no native calibration used as an internal axiom. -/
def InternalGuardedGraph : Prop := ∀ n (p : Program n)
 (itag ftag fval vtag ptag ctag rtag : Nat),
 (nodes p)[itag]? = some ⟨2,instanceCode⟩ →
 (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩ →
 (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 ∀ ctx (formula replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj
   (.imp (guards fval vtag formula replacement)
    (.equal (instanceCall itag formula replacement) (.succ (outputValue ftag ptag ctag rtag formula replacement))))
   (.imp (.neg (guards fval vtag formula replacement))
    (.equal (instanceCall itag formula replacement) .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.Targets
