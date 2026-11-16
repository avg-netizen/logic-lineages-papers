module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 HistoryRuleSuffix List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Exact constructors on all encoded raw formula lists, valid or malformed. -/
def NativeLine : Prop := ∀ isS (a b c : List Nat),
 evaluate (lineConstructor isS) (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ Encodable.encode c ::ᵥ nil) =
 Encodable.encode (nativeLine isS a b c)
/-- Exact original logical function on every numeric line; unmatched/malformed
lines use the unchanged fallback. No calibration is reflected internally. -/
def NativeRefinement : Prop := ∀ old : Program 1,
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf old) v = HistoryDispatcher.logicalFunction v
/-- Literal constructor graph with no validity or native-image premise. -/
def InternalLine : Prop := ∀ n (p : Program n) isS (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨3,lineConstructor isS⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (a b c : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall qtag a b c) (lineValue isS ptag ctag atag a b c)))
/-- Actual new leaf acceptance for either original K/S line. Only original
closed-formula validator premises; no logical/case success oracle or new-source
membership assumption. This is NOT current-root CORE/Fuel acceptance. -/
def InternalLogical : Prop := ∀ n (p : Program n) (old : Program 1) isS
 (qtag ltag ptag ctag atag fval : Nat),
 (nodes p)[qtag]? = some ⟨3,lineConstructor isS⟩ →
 (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 ∀ ctx (a b c : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards isS fval a b c)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineCall qtag a b c)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.Targets
