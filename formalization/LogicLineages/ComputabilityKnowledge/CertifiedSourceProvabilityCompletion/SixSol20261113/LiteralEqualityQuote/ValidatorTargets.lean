module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- The actual installed formula validator accepts the actual equality quotation
at arbitrary symbolic runtime values and binder context. Scanner/codec nodes
are obtained from the installed ASTs, not additional premises. This is syntax
acceptance only: no equality truth, proof-certificate acceptance or HB3. -/
def InternalValidator : Prop := ∀ k (t u : Term k) n (p : Program n)
 (qtag vtag : Nat),
 (nodes p)[qtag]? = some ⟨k,equalityQuote t u⟩ →
 (nodes p)[vtag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k) (binder : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxValidator.formulaCall vtag binder (quoteCall qtag values)) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralEqualityQuote.ValidatorTargets
