module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Arbitrary symbolic index/depth, unlike a fixed native Fin index. The actual
positive original difference graph witnesses index<depth internally. -/
def InternalVariableChunk : Prop := ∀ n (p : Program n) (stag ptag ctag dtag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩ →
 ∀ ctx (index depth positive : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (HistoryDifference.differenceCall dtag index depth) (.succ positive))
   (.equal (LiteralSyntaxScan.scanCall stag (termTasks ptag ctag depth) (variableChunk ctag index)) (.succ .zero))))
/-- Binder-aware runtime index emission: original pending index bound is 1+depth,
new term bound is depth. Closed replacement validity is an actual internal input
predicate. No native term witness, emitter success, or output validity premise. -/
def InternalIndexEmission : Prop := ∀ n (p : Program n) (etag vtag stag ptag ctag atag dtag : Nat),
 (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩ →
 ∀ ctx (index depth positive rest raw : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.imp (.equal (HistoryDifference.differenceCall dtag index (.succ depth)) (.succ positive))
    (.equal (LiteralSyntaxScan.scanCall stag (termTasks ptag ctag depth)
     (UniformClosedSubstitutionEmit.emitCall etag
      (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 2) (.succ depth) rest) index raw))
     (.succ .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Targets
