module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CodecProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution
theorem unary {arity ctx : Nat} (p : Program arity) (c d tag : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩)
 (a b : Term ctx) (hab : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (unaryValue c tag a) (unaryValue d tag b))) := by
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p c d 2 HistoryCodec.cons hc hd ctx
  (Term.numeral tag ::ᵥ a ::ᵥ nil)
 have harg := HistoryAppend.PositiveProof.binaryCongruence d (Term.numeral tag) (Term.numeral tag) a b
  (.logical (.reflexive _)) hab
 exact ⟨Logic.trans _ _ _ hcopy harg⟩
theorem binary {arity ctx : Nat} (p : Program arity) (c a d b tag : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩)
 (hb : (nodes p)[b]? = some ⟨2,HistoryAppend.append⟩)
 (x x' y y' : Term ctx)
 (hx : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal x x'))
 (hy : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal y y')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryValue c a tag x y) (binaryValue d b tag x' y'))) := by
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p a b 2 HistoryAppend.append ha hb ctx
  (x ::ᵥ y ::ᵥ nil)
 have hargs := HistoryAppend.PositiveProof.binaryCongruence b x x' y y' hx hy
 exact unary p c d tag hc hd _ _ (Logic.trans _ _ _ hcopy hargs)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CodecProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CodecProof
