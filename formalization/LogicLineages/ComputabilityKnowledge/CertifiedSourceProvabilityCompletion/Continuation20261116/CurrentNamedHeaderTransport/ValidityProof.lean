module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.InputGraphs
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem headerValid {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) (r s : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (CurrentNamedAliasCertificate.headerCode (tags I.previous) r s))) := by
 let K := tags I.previous
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old ar x I
 let v := r ::ᵥ s ::ᵥ nil
 have hv : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)).get i))) := by
  intro i
  simpa only [List.Vector.get_map] using PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current K.numeralTag H.hn G (v.get i)
 obtain ⟨hh⟩ := PrescribedRuntimeCallCongruence.ValidityProof.term p _ _ _ I.previous.current
  (PrescribedRuntimeSpecialization.runtimeEnvironment 2) header G (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) hv
 obtain ⟨he⟩ := InputGraphs.headerEncoding p K H r s
 have heq := HistoryLookup.DestructorProof.unaryCallCongruence I.previous.current.vtag _ _ he
 exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base (Support.equalitySymmetry _ _ heq)) hh⟩

theorem unaryEncoding {arity ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue K.ctag K.atag boundEnvironment unary nil raw)
   (callValue K (Term.numeral GorbowSourceRegistryPadding.functionTag) (raw ::ᵥ nil)))) := by
 simpa only [specializedValue,unary,List.Vector.map_cons,List.Vector.map_nil,
  termValue,UniformRuntimeEnvironmentAgreement.specialize,boundEnvironment,Fin.val_zero,Nat.not_lt_zero,dite_false,List.Vector.get_cons_zero] using
  CurrentCompositionCertificate.CallEncodingProof.call p K H.hc H.ha H.hn
   (UniformRuntimeEnvironmentAgreement.specialize boundEnvironment) (raw ::ᵥ nil)
   GorbowSourceRegistryPadding.functionTag ((.var 0 : Term 1) ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.ValidityProof
