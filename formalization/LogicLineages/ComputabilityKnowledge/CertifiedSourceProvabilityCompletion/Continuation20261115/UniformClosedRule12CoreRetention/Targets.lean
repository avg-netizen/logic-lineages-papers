module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Every original accepted certificate is retained at exactly the same code,
context, formula, index and fuel, including zero. No validity, recognizer
failure, shape, old/new run, state correspondence or leaf-implication premise.
Actual registry memberships alone supply the interface; all simulation must
be proved internally. No native calibration or source tuple identification. -/
def InternalCoreRetention : Prop := ∀ n (p : Program n)
 (valid logical arithmetic : Program 1) (x : Program 3)
 (oldTag newTag ptag ctag rightTag dropTag : Nat),
 (nodes p)[oldTag]? = some ⟨5,original valid logical arithmetic x⟩ →
 (nodes p)[newTag]? = some ⟨5,extended valid logical arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩ →
 ∀ ctx (index fuel context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralCheckerAcceptance.coreCall oldTag index fuel context formula certificate) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall newTag index fuel context formula certificate) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Targets
