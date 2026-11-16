module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Preflight
open GorbowPRProgram
theorem comparatorReflexivity : Targets.NativeCompiler = Targets.NativeCompiler := rfl
/-- These five AST checks are supporting checks, not additional semantic targets. -/
theorem zeroConstructor : compile .zero = CurrentBasicProducerProgram.program .zero := rfl
theorem successorConstructor : compile .succ = CurrentBasicProducerProgram.program .successor := rfl
theorem projectionConstructor {n : Nat} (i : Fin n) :
 compile (.projection i) = CurrentBasicProducerProgram.program (.projection i) := rfl
theorem compositionConstructor {m n : Nat} (f : Program n) (g : Fin n → Program m) :
 compile (.composition f g) = CurrentCompositionProducerProgram.program f g (compile f) (fun i => compile (g i)) := rfl
theorem recursionConstructor {n : Nat} (f : Program n) (g : Program (n+2)) :
 compile (.recursion f g) = CurrentRecursionProducerProgram.program f g (compile f) (compile g) := rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Preflight
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Preflight
