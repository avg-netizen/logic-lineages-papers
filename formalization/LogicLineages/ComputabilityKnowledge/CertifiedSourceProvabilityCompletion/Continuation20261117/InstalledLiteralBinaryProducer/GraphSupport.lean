module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem compose {arity m n ctx : Nat} (root : Program arity) (args : List.Vector (Term ctx) n)
 (f : Program m) (g : Fin m → Program n) (values : List.Vector (Term ctx) m) (out : Term ctx)
 (hg : ∀ i, Computes root (g i) args (values.get i))
 (hf : Computes root f values out) :
 Computes root (.composition f g) args out := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues root tag f g ht args values
  (fun i => hg i _ (Equations.argumentChild root tag f g ht i))
 obtain ⟨hf⟩ := hf _ (Equations.functionChild root tag f g ht)
 exact ⟨Logic.trans _ _ _ he hf⟩

def args {ctx : Nat} (a b c : Nat) (r s : Term ctx) : List.Vector (Term ctx) 5 :=
 Term.numeral a ::ᵥ Term.numeral b ::ᵥ Term.numeral c ::ᵥ r ::ᵥ s ::ᵥ nil

theorem pair {arity ctx : Nat} (root : Program arity) (a b c : Nat) (r s : Term ctx) :
 ∀ i, Computes root (pairInputs i) (args a b c r s) ((r ::ᵥ s ::ᵥ nil).get i) := by
 intro i
 refine Fin.cases ?_ (fun j => ?_) i
 · exact projection root _ (3 : Fin 5)
 · have hj : j = 0 := Fin.eq_zero j
   subst j
   exact projection root _ (4 : Fin 5)

theorem header {arity ctx : Nat} (root : Program arity) (a b c : Nat) (r s : Term ctx) :
 Computes root headerValue (args a b c r s) (GorbowRegistryTuple.headerTerm 2 0 [r,s]) :=
 compose root _ _ pairInputs (r ::ᵥ s ::ᵥ nil) _ (pair root a b c r s)
  (CurrentNamedHeaderTransport.InputGraphs.valueGraph root r s)

theorem numeral {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes root K) (a b c : Nat) (r s : Term ctx) :
 Computes root rawHeader (args a b c r s)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])) :=
 unary root _ LiteralNumeralPrefix.numeralCode K.numeralTag H.hn _ _ (header root a b c r s)

theorem call {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (a b c tag : Nat) (r s : Term ctx) :
 Computes root (rawCall tag) (args a b c r s)
  (RetainedBaseSourceCalculation.rawCall K tag (GorbowRegistryTuple.headerTerm 2 0 [r,s])) := by
 apply CurrentCompositionProducerProgram.CallEncoding.graph root _ K H
  (constant 5 tag) (rawHeader ::ᵥ nil) (Term.numeral tag)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s]) ::ᵥ nil)
  (constantValue root _ tag)
 intro i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 exact numeral root K ⟨H.hc,H.ha,H.hn⟩ a b c r s

theorem outputGraph {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (pF0 : Program 1)
 (hb : (nodes root)[12]? = some ⟨1,pF0⟩) (a b c : Nat) (r s : Term ctx) :
 Computes root (output pF0) (args a b c r s)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowPRDefiningEquations.call 12
   (GorbowRegistryTuple.headerTerm 2 0 [r,s] ::ᵥ nil))) := by
 apply unary root _ LiteralNumeralPrefix.numeralCode K.numeralTag H.hn _ _
 exact unary root _ pF0 12 hb _ _ (header root a b c r s)

theorem baseGraph {arity ctx : Nat} (root : Program arity) (pF0 : Program 1) (baseTag : Nat)
 (hb : (nodes root)[baseTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩)
 (a b c : Nat) (r s : Term ctx) :
 Computes root (baseCertificate pF0) (args a b c r s)
  (CurrentStructuralProducerCore.code baseTag 12 (GorbowRegistryTuple.headerTerm 2 0 [r,s] ::ᵥ nil)) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition root _ _ baseTag hb _
  (Term.numeral 12 ::ᵥ GorbowRegistryTuple.headerTerm 2 0 [r,s] ::ᵥ nil)
 intro i
 refine Fin.cases ?_ (fun j => ?_) i
 · exact constantValue root _ 12
 · have hj : j = 0 := Fin.eq_zero j
   subst j
   exact header root a b c r s

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphSupport
