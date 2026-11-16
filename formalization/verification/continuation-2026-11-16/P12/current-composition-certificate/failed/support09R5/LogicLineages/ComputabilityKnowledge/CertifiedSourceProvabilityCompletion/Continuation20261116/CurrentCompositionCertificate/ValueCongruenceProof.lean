module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CallEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValueCongruenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence
theorem tuples {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩) :
 ∀ n (a b : List.Vector (Term ctx) n),
 (∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (b.get i)))) →
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleValue J a.toList) (tupleValue J b.toList))) := by
 intro n
 induction n with
 | zero =>
  intro a b h
  rw [List.Vector.eq_nil a,List.Vector.eq_nil b]
  exact ⟨.logical (.reflexive _)⟩
 | succ n ih =>
  intro a b h
  obtain ⟨x,xs,rfl⟩ := List.Vector.exists_eq_cons a
  obtain ⟨y,ys,rfl⟩ := List.Vector.exists_eq_cons b
  obtain ⟨hh⟩ := h 0
  have ht : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (ys.get i))) := by
   intro i
   exact h i.succ
  obtain ⟨hs⟩ := ih xs ys ht
  obtain ⟨hp⟩ := CallEncodingProof.pairCongruence p J hc ha x y _ _ hh hs
  exact CodecProof.unary p J.ctag J.ctag 2 hc hc _ _ hp
theorem calls {arity ctx n : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (tag : Term ctx) (a b : List.Vector (Term ctx) n)
 (h : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (b.get i)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue J tag a) (callValue J tag b))) := by
 obtain ⟨ht⟩ := tuples p J hc ha n a b h
 obtain ⟨hp⟩ := CallEncodingProof.pairCongruence p J hc ha _ _ _ _ (.logical (.reflexive _)) ht
 obtain ⟨hh⟩ := CallEncodingProof.pairCongruence p J hc ha _ _ _ _ (.logical (.reflexive _)) hp
 exact CodecProof.unary p J.ctag J.ctag 5 hc hc _ _ hh
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValueCongruenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValueCongruenceProof
