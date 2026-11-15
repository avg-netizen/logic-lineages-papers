module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual unchanged original CORE: every accepted certificate is accepted at
the exact same code, context, formula, index and fuel (including zero).
No old/new run, shape, input-validity, state, leaf implication or acceptance
witness is an additional premise. Literal registry memberships supply the
entire interface. This is the fixed unary equality-template extension only. -/
def InternalCoreRetention : Prop := ∀ (lhs rhs : Term 1) n (p : Program n)
 (valid logical arithmetic : Program 1) (x : Program 3)
 (oldTag newTag ptag ctag rightTag dropTag : Nat),
 (nodes p)[oldTag]? = some ⟨5,original valid logical arithmetic x⟩ →
 (nodes p)[newTag]? = some ⟨5,extended lhs rhs valid logical arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[rightTag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩ →
 ∀ ctx (index fuel context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralCheckerAcceptance.coreCall oldTag index fuel context formula certificate) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall newTag index fuel context formula certificate) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.EqualityInstantiationCoreRetention.Targets
