module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
def NativeLine : Prop := ∀ formula left right : List Nat,
 evaluate lineConstructor (Encodable.encode formula ::ᵥ Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) =
 Encodable.encode (nativeLine formula left right)
def NativeRefinement : Prop := ∀ old : Program 1,
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf old) v = HistoryDispatcher.logicalFunction v
/-- Unconditional actual constructor graph, including malformed codes. -/
def InternalLine : Prop := ∀ n (p : Program n) (qtag caseTag predTag ptag ctag : Nat),
 (nodes p)[qtag]? = some ⟨3,lineConstructor⟩ →
 (nodes p)[caseTag]? = some ⟨1,UniformClosedCase12.caseCode⟩ →
 (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (formula left right : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall qtag formula left right) (lineValue caseTag predTag ptag ctag formula left right)))
/-- Original runtime guards only, internal acceptance of the actual new leaf.
No native image, successful case12, supplied conclusion validity or source
installation is assumed. -/
def InternalLogical : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag caseTag predTag ptag ctag fval vtag : Nat),
 (nodes p)[qtag]? = some ⟨3,lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩ →
 (nodes p)[caseTag]? = some ⟨1,UniformClosedCase12.caseCode⟩ →
 (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (formula left right : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards fval vtag formula left right)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineCall qtag formula left right)) (.succ .zero))))
/-- Literal case13 fallback success is preserved on EVERY runtime line.
Both tags are actual memberships; duplicate occurrences are not identified. -/
def InternalRetainsCase13 : Prop := ∀ n (p : Program n) (old : Program 1) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨1,UniformClosedRule13.logicalLeaf old⟩ →
 (nodes p)[newTag]? = some ⟨1,logicalLeaf old⟩ →
 ∀ ctx (line : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall oldTag line) (.succ .zero))
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall newTag line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.Targets
