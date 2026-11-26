module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Every accepted original certificate survives the actual nested K/S leaf
extension, at identical code, context, formula, index and fuel (including zero).
Only actual old/new core and codec memberships are supplied. No intermediate
core installation, simulation, validity, shape, recognizer failure or leaf
retention premise is permitted. This is not same-source reinstallation or HB3. -/
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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Targets
