module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Exact original LogicalInstance.reflexive annotation after numeral
substitution, calibrated on every runtime vector. -/
def NativeCalibration : Prop := ∀ k (t : Term k) (values : List.Vector Nat k),
 evaluate (annotationQuote t) values = Encodable.encode
  (GorbowLogicalAxiomCode.encode (GorbowPACore.LogicalInstance.reflexive
   (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) t)))
/-- Actual installed AST equation on arbitrary symbolic inputs. The same
term quotation may occur at any installed tag, transported by registry
coherence. No logical-leaf acceptance or producer correctness is assumed. -/
def InternalEquation : Prop := ∀ k (t : Term k) n (p : Program n)
 (qtag ttag ptag ctag : Nat),
 (nodes p)[qtag]? = some ⟨k,annotationQuote t⟩ →
 (nodes p)[ttag]? = some ⟨k,LiteralTemplateQuote.templateQuote t⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (quoteCall qtag values)
   (annotationValue ptag ctag (LiteralTemplateQuote.quoteCall ttag values))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.Targets
