module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherPrimitivesProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryRuleSuffix
/-- Binary graph input transport in the unchanged internal language. -/
theorem binaryInputs {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (q : Program 2)
 (a b a' b' out : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal a a'))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal b b'))
 (hq : Computes p G q (a' ::ᵥ b' ::ᵥ nil) out) : Computes p G q (a ::ᵥ b ::ᵥ nil) out := by
 intro tag ht
 obtain ⟨hv⟩ := hq tag ht
 have hc := callCongruence (T := GorbowPRNumeralCalculation.Theory p) (G := G) tag
  (a ::ᵥ b ::ᵥ nil) (a' ::ᵥ b' ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact ha
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 exact ⟨localTrans _ _ _ hc hv⟩
theorem differenceDiagonal {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (a : Term ctx) :
 Computes p G HistoryCodec.difference (a ::ᵥ a ::ᵥ nil) .zero := by
 intro tag ht
 obtain ⟨h⟩ := HistoryDecoder.StepInvariantProof.differenceDiagonal p tag ht a
 exact ⟨.base h⟩
theorem differenceBelow {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (token depth gap : Term ctx)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (.add token (.succ gap)) depth)) :
 Computes p G HistoryCodec.difference (token ::ᵥ depth ::ᵥ nil) (.succ gap) := by
 apply binaryInputs p G HistoryCodec.difference token depth token (.add token (.succ gap)) (.succ gap)
  (.base (.logical (.reflexive token))) (HistoryOrder.StepProof.localSym _ _ h)
 intro tag ht
 obtain ⟨hc⟩ := HistoryDifference.ArithmeticProof.differenceCancel n p tag ht ctx token (.succ gap)
 exact ⟨.base hc⟩
theorem differenceAbove {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (token depth gap : Term ctx)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (.add depth (.succ gap)) token)) :
 Computes p G HistoryCodec.difference (token ::ᵥ depth ::ᵥ nil) .zero := by
 apply binaryInputs p G HistoryCodec.difference token depth (.add depth (.succ gap)) depth .zero
  (HistoryOrder.StepProof.localSym _ _ h) (.base (.logical (.reflexive depth)))
 intro tag ht
 obtain ⟨hc⟩ := HistoryDifference.ArithmeticProof.differenceSaturate n p tag ht ctx depth (.succ gap)
 exact ⟨.base hc⟩
theorem equalAbove {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (token depth gap : Term ctx)
 (h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (.add depth (.succ gap)) token)) :
 Computes p G equalCode (token ::ᵥ depth ::ᵥ nil) .zero := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (.add depth (.succ gap)) depth
 have hh : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hs := (HistoryOrder.StepProof.localSym _ _ hh).discharge.finish
 have hn : Derivation T (.neg E) := Hilbert.modusTollens hs (HistoryCancellation.OrderSupportProof.positiveGapImpossible depth gap)
 apply binaryInputs p G equalCode token depth (.add depth (.succ gap)) depth .zero
  (HistoryOrder.StepProof.localSym _ _ h) (.base (.logical (.reflexive depth)))
 exact equalFalse p G (.add depth (.succ gap)) depth hn
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ArithmeticProof
