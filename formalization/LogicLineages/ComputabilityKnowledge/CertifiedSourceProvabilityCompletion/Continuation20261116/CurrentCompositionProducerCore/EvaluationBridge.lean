module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.EvaluationBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem argument {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (I : CurrentCompositionProducerProgram.Installation p f g F G J) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) (i : Fin n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call (J.argumentTags i) inputs) ((childValues f g target inputs).get i))) := by
 simp only [childValues,List.Vector.get_ofFn]
 exact GorbowPRInternalCoherence.Proof.registryCoherence arity p (J.argumentTags i) (target+argumentTag f g i) m (g i)
  (I.hg i) (Equations.argumentChild p target f g ht i) ctx inputs

theorem root {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call target inputs) (call (target+1) (childValues f g target inputs)))) := by
 apply Equations.compositionValues p target f g ht inputs (childValues f g target inputs)
 intro i
 simp only [childValues,List.Vector.get_ofFn]
 exact ⟨.logical (.reflexive _)⟩

theorem result {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (I : CurrentCompositionProducerProgram.Installation p f g F G J) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call J.functionTag (List.Vector.ofFn (fun i => call (J.argumentTags i) inputs)))
   (call (target+1) (childValues f g target inputs)))) := by
 obtain ⟨hs⟩ := SpecializationCopy.finiteWitness n _ (argument p f g F G J I target ht inputs)
 have hv := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) J.functionTag
  (List.Vector.ofFn (fun i => call (J.argumentTags i) inputs)) (childValues f g target inputs) (fun i => by
   simp only [List.Vector.get_ofFn]
   exact hs i)
 obtain ⟨hf⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p J.functionTag (target+1) n f
  I.hf (Equations.functionChild p target f g ht) ctx (childValues f g target inputs)
 exact ⟨Logic.trans _ _ _ hv hf⟩

theorem functionCode {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (I : CurrentCompositionProducerProgram.Installation p f g F G J) (target : Nat)
 (ht : (nodes p)[target]? = some ⟨m,Program.composition f g⟩) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call J.functionProducerTag (.succ (Term.numeral target) ::ᵥ List.Vector.ofFn (fun i => call (J.argumentTags i) inputs)))
   (producerCode J.functionProducerTag (target+1) (childValues f g target inputs)))) := by
 obtain ⟨hs⟩ := SpecializationCopy.finiteWitness n _ (argument p f g F G J I target ht inputs)
 apply Nonempty.intro
 apply Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) J.functionProducerTag
 intro i
 cases i using Fin.cases with
 | zero => exact .logical (.reflexive _)
 | succ i =>
  simp only [List.Vector.get_cons_succ,List.Vector.get_ofFn]
  exact hs i

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.EvaluationBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.EvaluationBridge
