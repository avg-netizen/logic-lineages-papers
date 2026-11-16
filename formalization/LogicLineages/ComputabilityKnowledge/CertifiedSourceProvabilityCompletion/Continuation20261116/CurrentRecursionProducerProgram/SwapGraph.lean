module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
theorem composition {arity n k ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) n)
 (f : Program k) (g : Fin k → Program n) (values : List.Vector (Term ctx) k) (v : Term ctx)
 (hg : ∀ i, Computes p (g i) args (values.get i)) (hf : Computes p f values v) :
 Computes p (.composition f g) args v := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag f g ht args values
  (fun i => hg i _ (Equations.argumentChild p tag f g ht i))
 obtain ⟨hf⟩ := hf _ (Equations.functionChild p tag f g ht)
 exact ⟨Logic.trans _ _ _ he hf⟩

theorem arguments {arity m ctx : Nat} (p : Program arity) (a b : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin (m+2)) :
 Computes p (swapInputs m i) (a ::ᵥ b ::ᵥ inputs) ((b ::ᵥ a ::ᵥ inputs).get i) := by
 cases i using Fin.cases with
 | zero => exact projection p _ 1
 | succ i => cases i using Fin.cases with
   | zero => exact projection p _ 0
   | succ i => exact projection p _ i.succ.succ

theorem swapCall {arity m ctx : Nat} (p : Program arity) (q : Program (m+2)) (qtag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨m+2,q⟩) (a b : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (swap q) (a ::ᵥ b ::ᵥ inputs) (call qtag (b ::ᵥ a ::ᵥ inputs)) :=
 CurrentRecursionAccumulator.GraphSupport.composition p _ q qtag hq _ _ (arguments p a b inputs)

theorem atCounter {arity m ctx : Nat} (p : Program arity) (q : Program (m+2)) (qtag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨m+2,q⟩) (counter previous target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (.composition (swap q) (CurrentRecursionAccumulator.atCounter (m+1)))
  (counter ::ᵥ previous ::ᵥ target ::ᵥ inputs) (call qtag (target ::ᵥ counter ::ᵥ inputs)) := by
 apply composition p _ (swap q) _ (counter ::ᵥ target ::ᵥ inputs) _ ?_ (swapCall p q qtag hq counter target inputs)
 intro i
 cases i using Fin.cases with
 | zero => exact projection p _ 0
 | succ i => exact projection p _ i.succ.succ

theorem atSuccessor {arity m ctx : Nat} (p : Program arity) (q : Program (m+2)) (qtag : Nat)
 (hq : (nodes p)[qtag]? = some ⟨m+2,q⟩) (counter previous target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (.composition (swap q) (CurrentRecursionAccumulator.atSuccessor (m+1)))
  (counter ::ᵥ previous ::ᵥ target ::ᵥ inputs) (call qtag (target ::ᵥ .succ counter ::ᵥ inputs)) := by
 apply composition p _ (swap q) _ (.succ counter ::ᵥ target ::ᵥ inputs) _ ?_
  (swapCall p q qtag hq (.succ counter) target inputs)
 intro i
 cases i using Fin.cases with
 | zero => exact CurrentRecursionAccumulator.GraphSupport.successorProjection p _ 0
 | succ i => exact projection p _ i.succ.succ

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapGraph
