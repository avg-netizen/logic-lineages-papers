module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open TwoSol20261113.ReflexivityRecognizer
/-- All finite raw streams, including syntactically invalid streams. Exact
original context0/rule0/tag11/one-argument/zero-reference line encoding. -/
def NativeLine : Prop := ∀ raw : List Nat,
 evaluate lineConstructor (Encodable.encode raw ::ᵥ nil) =
 Encodable.encode (NativeProof.rawLine raw)
/-- Independent internal constructor equation at arbitrary symbolic raw code. -/
def InternalLine : Prop := ∀ n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,lineConstructor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall qtag raw) (lineValue ptag ctag atag raw)))
/-- Genuine INTERNAL implication from actual term-validator success to actual
logical-leaf success on the universal line constructor. Validity is an object-
language antecedent, never an externally supplied successful derivation.
This does not yet assert dispatcher/CORE/Fuel acceptance, source installation,
coherent computation, HB3 or a whole numbered target. -/
def InternalLogical : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (leafCall vtag raw) (.succ .zero))
   (.equal (leafCall ltag (lineCall qtag raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.Targets
