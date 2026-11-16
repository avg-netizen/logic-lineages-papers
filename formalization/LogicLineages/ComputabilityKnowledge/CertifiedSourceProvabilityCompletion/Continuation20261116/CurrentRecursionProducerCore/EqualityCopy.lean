module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallTransport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.EqualityCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

theorem rule12 {arity ctx : Nat} (p : Program arity) (c r d s : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (hr : (nodes p)[r]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩) (hs : (nodes p)[s]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (f f' x x' y y' : Term ctx)
 (hf : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal f f'))
 (hx : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal x x'))
 (hy : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal y y')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule12Certificate.certificate c r f x y) (UniformClosedRule12Certificate.certificate d s f' x' y'))) := by
 have hargs : ∀ j, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((f ::ᵥ x ::ᵥ y ::ᵥ nil).get j) ((f' ::ᵥ x' ::ᵥ y' ::ᵥ nil).get j)) := by
  intro j
  cases j using Fin.cases with
  | zero => exact hf
  | succ j => cases j using Fin.cases with
    | zero => exact hx
    | succ j => cases j using Fin.cases with
      | zero => exact hy
      | succ j => exact Fin.elim0 j
 obtain ⟨hl⟩ := CallTransport.callCopy p UniformClosedRule12.lineConstructor r s hr hs _ _ hargs
 exact CallTransport.singleton p c d hc hd _ _ hl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.EqualityCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.EqualityCopy
