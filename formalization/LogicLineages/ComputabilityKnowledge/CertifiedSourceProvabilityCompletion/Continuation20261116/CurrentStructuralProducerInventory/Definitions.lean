module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentStructuralProducerCompiler

/-- Concrete local items. Every recursion includes the EXACT accepted extended
extra, not a replacement record of assumed coverage. -/
def localItems {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) : {n : Nat} → Program n → List Packed
 | n, q => [⟨n,q⟩,⟨n+1,compile q⟩] ++ match q with
   | .recursion f g => [⟨6,CurrentRecursionProducerSource.extendedExtra installed lhs rhs t old a baseX
      f g (compile f) (compile g)⟩]
   | _ => []

/-- Finite structural inventory, constructed before any registry tags or
source tuple are selected. Duplicate ASTs are deliberately permitted. -/
def inventory {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) : {n : Nat} → Program n → List Packed
 | _, .zero => localItems installed lhs rhs t old a baseX .zero
 | _, .succ => localItems installed lhs rhs t old a baseX .succ
 | _, .projection i => localItems installed lhs rhs t old a baseX (.projection i)
 | _, .composition f g => localItems installed lhs rhs t old a baseX (.composition f g) ++
   inventory installed lhs rhs t old a baseX f ++
   (List.ofFn (fun i => inventory installed lhs rhs t old a baseX (g i))).flatten
 | _, .recursion f g => localItems installed lhs rhs t old a baseX (.recursion f g) ++
   inventory installed lhs rhs t old a baseX f ++ inventory installed lhs rhs t old a baseX g

def carrier {k n : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (q : Program n) : Program 6 :=
 LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.bundle (inventory installed lhs rhs t old a baseX q)

/-- Existing constructor interfaces, with evaluator occurrence fixed by the
caller. Producer/auxiliary occurrences remain independently chosen. -/
def InstalledAt {arity k : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (target producerTag : Nat) : {n : Nat} → Program n → Prop
 | _, .zero => ∃ J, CurrentBasicProducerProgram.Installation p J
 | _, .succ => ∃ J, CurrentBasicProducerProgram.Installation p J
 | _, .projection _ => ∃ J, CurrentBasicProducerProgram.Installation p J
 | _, .composition f g => ∃ J,
   CurrentCompositionProducerProgram.Installation p f g (compile f) (fun i => compile (g i)) J ∧
   J.functionTag = target+1 ∧ (∀ i, J.argumentTags i = target+argumentTag f g i)
 | _, .recursion f g => ∃ R : CurrentRecursionProducerSource.Installation p
   installed lhs rhs t old a baseX f g (compile f) (compile g),
   R.qTag = target ∧ R.producer.publicTag = producerTag
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory
