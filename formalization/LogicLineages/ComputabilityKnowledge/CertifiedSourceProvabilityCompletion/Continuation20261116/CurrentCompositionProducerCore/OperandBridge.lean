module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.EvaluationBridge
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.OriginalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.OperandBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem numeral {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (a b : Term ctx) (h : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.numeralTag a) (LiteralNumeralPrefix.numeralCall K.numeralTag b))) := by
 apply CallTransport.callCopy p LiteralNumeralPrefix.numeralCode J.numeralTag K.numeralTag H.hn L.hn (a ::ᵥ nil) (b ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => exact Fin.elim0 i

theorem leftArgument {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (J K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentCallCongruenceProgram.Installation p J)
 (L : CurrentCallCongruenceProgram.Installation p K) (target : Nat) (inputs : List.Vector (Term ctx) m) (i : Fin n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue J (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) (Term.numeral target))
   (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
   (callValue K (Term.numeral (target+argumentTag f g i)) (inputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag))))) := by
 rw [CurrentRecursionStepProgram.TemplateSyntax.shiftNumeral]
 exact CodecBridge.call p J K (TupleCopy.nodes p J H) (TupleCopy.nodes p K L) _ inputs

theorem rightArgument {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (H : CurrentCompositionProducerProgram.Installation p f g F G J) (K : PrescribedRuntimeCallCongruence.Tags)
 (L : CurrentCallCongruenceProgram.Installation p K) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) (i : Fin n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.C.numeralTag (call (J.argumentTags i) inputs))
   (LiteralNumeralPrefix.numeralCall K.numeralTag ((childValues f g target inputs).get i)))) := by
 obtain ⟨h⟩ := EvaluationBridge.argument p f g F G J H target ht inputs i
 exact numeral p J.C K H.primitives L _ _ h

theorem output {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (H : CurrentCompositionProducerProgram.Installation p f g F G J) (K : PrescribedRuntimeCallCongruence.Tags)
 (L : CurrentCallCongruenceProgram.Installation p K) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.C.numeralTag (call J.functionTag (List.Vector.ofFn (fun i => call (J.argumentTags i) inputs))))
   (LiteralNumeralPrefix.numeralCall K.numeralTag (call (target+1) (childValues f g target inputs))))) := by
 obtain ⟨h⟩ := EvaluationBridge.result p f g F G J H target ht inputs
 exact numeral p J.C K H.primitives L _ _ h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.OperandBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.OperandBridge
