module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.BinaryCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.TupleCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem nodes {arity : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) : CodecBridge.Nodes p J := ⟨H.hc,H.ha,H.hn⟩

theorem certificate {arity ctx n : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (xs ys codes xs' ys' codes' : List.Vector (Term ctx) n)
 (hx : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (xs'.get i)))
 (hy : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (ys.get i) (ys'.get i)))
 (hc : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (codes.get i) (codes'.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleCertificate J xs ys codes) (tupleCertificate K xs' ys' codes'))) := by
 induction n with
 | zero => exact ScalarCopy.reflexivity p J K H L _ _ (.logical (.reflexive _))
 | succ n ih =>
  have hxt : ∀ i : Fin n, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.tail.get i) (xs'.tail.get i)) := by
   intro i; rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]; exact hx i.succ
  have hyt : ∀ i : Fin n, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (ys.tail.get i) (ys'.tail.get i)) := by
   intro i; rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]; exact hy i.succ
  have hct : ∀ i : Fin n, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (codes.tail.get i) (codes'.tail.get i)) := by
   intro i; rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]; exact hc i.succ
  have hx0 : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal xs.head xs'.head) := by simpa only [List.Vector.get_zero] using hx 0
  have hy0 : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal ys.head ys'.head) := by simpa only [List.Vector.get_zero] using hy 0
  have hc0 : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal codes.head codes'.head) := by simpa only [List.Vector.get_zero] using hc 0
  obtain ⟨hxtv⟩ := CallRawCopy.tuple p J K (nodes p J H) (nodes p K L) n xs.tail xs'.tail hxt
  obtain ⟨hytv⟩ := CallRawCopy.tuple p J K (nodes p J H) (nodes p K L) n ys.tail ys'.tail hyt
  obtain ⟨hctv⟩ := ih xs.tail ys.tail codes.tail xs'.tail ys'.tail codes'.tail hxt hyt hct
  obtain ⟨hp⟩ := BinaryCopy.pair p J K H L _ _ _ _ _ _ _ _ _ _ _ _ hx0 hxtv hy0 hytv hc0 hctv
  obtain ⟨hleft⟩ := CodecBridge.pair p J K (nodes p J H) (nodes p K L) _ _ _ _ hx0 hxtv
  obtain ⟨hright⟩ := CodecBridge.pair p J K (nodes p J H) (nodes p K L) _ _ _ _ hy0 hytv
  exact ScalarCopy.ordinary p J K H L boundEnvironment (.succ (.var 0)) nil nil _ _ _ _ _ _
   (fun i => Fin.elim0 i) hleft hright hp

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.TupleCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.TupleCopy
