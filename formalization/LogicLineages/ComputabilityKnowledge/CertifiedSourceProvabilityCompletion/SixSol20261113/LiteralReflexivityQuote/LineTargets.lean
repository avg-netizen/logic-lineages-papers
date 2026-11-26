module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Exact ORIGINAL closed logicalLine encoding after numeral substitution. -/
def NativeCalibration : Prop := ∀ k (t : Term k) (values : List.Vector Nat k),
 evaluate (lineQuote t) values = Encodable.encode
  (GorbowProofChecker.logicalLine (GorbowPACore.LogicalInstance.reflexive
   (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) t)))
/-- Symbolic actual line constructor equation only. This does not assert that
an opaque logical leaf accepts the line, nor certificate acceptance or HB3. -/
def InternalEquation : Prop := ∀ k (t : Term k) n (p : Program n)
 (qtag etag ttag ptag ctag : Nat),
 (nodes p)[qtag]? = some ⟨k,lineQuote t⟩ →
 (nodes p)[etag]? = some ⟨k,LiteralEqualityQuote.equalityQuote t t⟩ →
 (nodes p)[ttag]? = some ⟨k,LiteralTemplateQuote.templateQuote t⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (quoteCall qtag values)
   (lineValue ptag ctag (LiteralEqualityQuote.quoteCall etag values)
    (LiteralTemplateQuote.quoteCall ttag values))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.LineTargets
