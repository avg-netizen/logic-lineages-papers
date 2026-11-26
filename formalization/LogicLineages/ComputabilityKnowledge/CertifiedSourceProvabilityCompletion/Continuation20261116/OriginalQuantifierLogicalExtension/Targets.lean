module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
/-- Complete all-Nat branch law with arbitrary fallback AND original native
logicalFunction calibration when the fallback is calibrated. No malformed
line is accepted merely because its annotation resembles2/10. -/
def Native : Prop :=
 (∀ (old : Program 1) (v : List.Vector Nat 1),
  evaluate (logicalLeaf old) v =
   if evaluate (recognizer true) v = 0 then
    (if evaluate (recognizer false) v = 0 then evaluate old v else 1)
   else 1) ∧
 (∀ (old : Program 1), (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
  ∀ v, evaluate (logicalLeaf old) v = HistoryDispatcher.logicalFunction v)
/-- Symbolic guarded acceptance by the ACTUAL extended logical leaf, not
current-I CORE and not membership of an unrelated extra constructor. Arity1
matrix guard for duality; arity0 guards for contraposition. -/
def InternalLogical : Prop := ∀ arity (p : Program arity) (old : Program 1) (isExists : Bool)
 (lineTag leafTag ptag ctag atag fval : Nat),
 (nodes p)[lineTag]? = some ⟨2,OriginalQuantifierLogicalProducers.lineConstructor isExists⟩ →
 (nodes p)[leafTag]? = some ⟨1,logicalLeaf old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ →
 ∀ ctx (a b : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards isExists fval a b)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall leafTag
    (OriginalQuantifierLogicalProducers.lineCall lineTag a b)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.Targets
