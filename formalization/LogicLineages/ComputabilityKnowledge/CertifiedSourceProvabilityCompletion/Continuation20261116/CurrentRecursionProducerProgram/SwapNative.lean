module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapNative
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem arguments {m : Nat} (a b : Nat) (inputs : List.Vector Nat m) :
 List.Vector.ofFn (fun i => evaluate (swapInputs m i) (a ::ᵥ b ::ᵥ inputs)) = b ::ᵥ a ::ᵥ inputs := by
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => cases i using Fin.cases with
   | zero => rfl
   | succ i => simp only [List.Vector.get_ofFn,swapInputs,Fin.cases_succ,evaluate,List.Vector.get_cons_succ]

theorem swapEval {m : Nat} (q : Program (m+2)) (a b : Nat) (inputs : List.Vector Nat m) :
 evaluate (swap q) (a ::ᵥ b ::ᵥ inputs) = evaluate q (b ::ᵥ a ::ᵥ inputs) := by
 change evaluate q (List.Vector.ofFn (fun i => evaluate (swapInputs m i) (a ::ᵥ b ::ᵥ inputs))) = _
 rw [arguments]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapNative
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapNative
