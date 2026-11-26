module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113
/-- All vectors, including arbitrary malformed term streams. -/
def NativeTerm : Prop := ∀ raw : List Nat,
 evaluate termValidator (Encodable.encode raw ::ᵥ nil) =
 HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 raw)
/-- ORIGINAL logicalFunction on every vector; the fallback retains all other schemes. -/
def NativeRefinement : Prop := ∀ old : Program 1,
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf old) v = HistoryDispatcher.logicalFunction v
/-- Independent internal acceptance on arbitrary runtime quoted term values. -/
def InternalTerm : Prop := ∀ k (t : Term k) n (p : Program n) (ttag vtag ptag ctag atag : Nat),
 (nodes p)[ttag]? = some ⟨k,LiteralTemplateQuote.templateQuote t⟩ →
 (nodes p)[vtag]? = some ⟨1,termValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall vtag (LiteralTemplateQuote.quoteCall ttag values)) (.succ .zero)))
/-- Actual logical leaf accepts the actual ORIGINAL complete runtime line.
Only concrete AST installation premises occur; no native fact is reflected. -/
def InternalLogical : Prop := ∀ k (t : Term k) (old : Program 1) n (p : Program n)
 (ltag qtag etag ttag ptag ctag atag vtag : Nat),
 (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩ →
 (nodes p)[qtag]? = some ⟨k,LiteralReflexivityQuote.lineQuote t⟩ →
 (nodes p)[etag]? = some ⟨k,LiteralEqualityQuote.equalityQuote t t⟩ →
 (nodes p)[ttag]? = some ⟨k,LiteralTemplateQuote.templateQuote t⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,termValidator⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall ltag (LiteralReflexivityQuote.quoteCall qtag values)) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.Targets
