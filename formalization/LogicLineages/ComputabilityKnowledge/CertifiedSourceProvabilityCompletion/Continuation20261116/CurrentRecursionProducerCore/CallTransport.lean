module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallTransport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

theorem callCopy {arity n ctx : Nat} (p : Program arity) (q : Program n) (a b : Nat)
 (ha : (nodes p)[a]? = some ⟨n,q⟩) (hb : (nodes p)[b]? = some ⟨n,q⟩)
 (xs ys : List.Vector (Term ctx) n)
 (hargs : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (ys.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call a xs) (call b ys))) := by
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p a b n q ha hb ctx xs
 exact ⟨Logic.trans _ _ _ hc (Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) b xs ys hargs)⟩

theorem singleton {arity ctx : Nat} (p : Program arity) (c d : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩)
 (a b : Term ctx) (h : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.consCall c a .zero) (HistoryLookup.consCall d b .zero))) := by
 apply callCopy p HistoryCodec.cons c d hc hd (a ::ᵥ .zero ::ᵥ nil) (b ::ᵥ .zero ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => exact Fin.elim0 i

theorem mp {arity ctx : Nat} (p : Program arity) (a b : Nat)
 (ha : (nodes p)[a]? = some ⟨4,LiteralRawMP.constructor⟩) (hb : (nodes p)[b]? = some ⟨4,LiteralRawMP.constructor⟩)
 (f f' i i' x x' : Term ctx)
 (hf : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal f f'))
 (hi : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal i i'))
 (hx : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal x x')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralMPRun.certificate a .zero f i x) (LiteralMPRun.certificate b .zero f' i' x'))) := by
 apply callCopy p LiteralRawMP.constructor a b ha hb (.zero ::ᵥ f ::ᵥ i ::ᵥ x ::ᵥ nil) (.zero ::ᵥ f' ::ᵥ i' ::ᵥ x' ::ᵥ nil)
 intro j
 cases j using Fin.cases with
 | zero => exact .logical (.reflexive _)
 | succ j => cases j using Fin.cases with
   | zero => exact hf
   | succ j => cases j using Fin.cases with
     | zero => exact hi
     | succ j => cases j using Fin.cases with
       | zero => exact hx
       | succ j => exact Fin.elim0 j

theorem rule13 {arity ctx : Nat} (p : Program arity) (c r d s : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (hr : (nodes p)[r]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩) (hs : (nodes p)[s]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (f f' x x' : Term ctx)
 (hf : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal f f'))
 (hx : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal x x')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule13Certificate.certificate c r f x) (UniformClosedRule13Certificate.certificate d s f' x'))) := by
 have hargs : ∀ j, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((f ::ᵥ x ::ᵥ nil).get j) ((f' ::ᵥ x' ::ᵥ nil).get j)) := by
  intro j
  cases j using Fin.cases with
  | zero => exact hf
  | succ j => cases j using Fin.cases with
    | zero => exact hx
    | succ j => exact Fin.elim0 j
 obtain ⟨hl⟩ := callCopy p UniformClosedRule13.lineConstructor r s hr hs _ _ hargs
 exact singleton p c d hc hd _ _ hl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallTransport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallTransport
