module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RhsEncoding
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RootEncoding
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open FixedFormulaSubstitution PrescribedRuntimeCallCongruence
theorem root {arity k n ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhsTerm : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhsTerm t old a x)
 (kind : Kind n) (target : Nat) (ht : (nodes p)[target]? = some ⟨n,evaluator kind⟩)
 (inputs : List.Vector (Term ctx) n) :
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag
   (rootFormula kind target) (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
   (CurrentRecursionProducerCore.childFormula J target inputs))) := by
 dsimp only
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 let raw := inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)
 let e := PrescribedRuntimeSpecialization.runtimeEnvironment n
 have H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p installed lhs rhsTerm t old a x I
 obtain ⟨hf⟩ := CurrentRecursionProducerCore.FormulaCopy.formula p I.previous.previous.current.ctag I.previous.previous.current.atag
  J.ctag J.atag I.previous.previous.current.h_ctag I.previous.previous.current.h_atag H.hc H.ha raw e (rootFormula kind target)
 obtain ⟨hl⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J H.hc H.ha H.hn e raw target (argumentVariables n)
 rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues] at hl
 obtain ⟨hr⟩ := RhsEncoding.actual p J H kind target ht inputs
 obtain ⟨he⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 0 H.hc H.ha H.hc H.ha
  _ _ _ _ hl hr
 exact ⟨Logic.trans _ _ _ hf he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RootEncoding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RootEncoding
