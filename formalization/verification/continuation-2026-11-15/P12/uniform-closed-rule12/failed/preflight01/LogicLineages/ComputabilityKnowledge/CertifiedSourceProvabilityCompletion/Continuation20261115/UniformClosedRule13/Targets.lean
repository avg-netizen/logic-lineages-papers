module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
/-- All raw token lists; malformed instances use original Option.getD[]. -/
def NativeLine : Prop := ∀ (formula replacement : List Nat),
 evaluate lineConstructor (Encodable.encode formula ::ᵥ Encodable.encode replacement ::ᵥ nil) =
 Encodable.encode (nativeLine formula replacement)
/-- Every numeric input line and original logicalFunction, preserving fallback.
Not restricted to generated lines or native Formula/Term images. -/
def NativeRefinement : Prop := ∀ (old : Program 1),
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf old) v = HistoryDispatcher.logicalFunction v
/-- Actual constructor graph, including malformed runtime codes, without guards. -/
def InternalLine : Prop := ∀ n (p : Program n) (qtag caseTag predTag ptag ctag : Nat),
 (nodes p)[qtag]? = some ⟨2,lineConstructor⟩ →
 (nodes p)[caseTag]? = some ⟨1,UniformClosedCase13.caseCode⟩ →
 (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (formula replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall qtag formula replacement) (lineValue caseTag predTag ptag ctag formula replacement)))
/-- Genuine internal logical-leaf acceptance on arbitrary runtime codes from
exact original formula1/closed-term0 guards, no native reflection. -/
def InternalLogical : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag caseTag predTag ptag ctag fval vtag : Nat),
 (nodes p)[qtag]? = some ⟨2,lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩ →
 (nodes p)[caseTag]? = some ⟨1,UniformClosedCase13.caseCode⟩ →
 (nodes p)[predTag]? = some ⟨1,HistoryCodec.predecessor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (formula replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards fval vtag formula replacement)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineCall qtag formula replacement)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13.Targets
