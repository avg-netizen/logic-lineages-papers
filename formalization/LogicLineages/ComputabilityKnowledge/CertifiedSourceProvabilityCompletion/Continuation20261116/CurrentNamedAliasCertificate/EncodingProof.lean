module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootEncodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallRawCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.EncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence GorbowRegistryTuple
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentCompositionCertificate.CallEncodingProof

theorem header {arity n depth inputs ctx m : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p J)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (tag : Nat)
 (args : List.Vector (Term n) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw (headerTerm m tag args.toList))
   (headerValue J (Term.numeral tag) (args.map (termValue J.ctag J.atag e raw))))) := by
 obtain ⟨hArity⟩ := numeral p J.ctag J.atag H.hc e raw m
 obtain ⟨hTag⟩ := numeral p J.ctag J.atag H.hc e raw tag
 obtain ⟨hNum⟩ := ValueTraceProof.numeral (ctx := ctx) p J H.hn tag
 have hTag' := Logic.trans _ _ _ hTag (Support.equalitySymmetry _ _ hNum)
 obtain ⟨hp⟩ := pairCongruence p J H.hc H.ha _ _ _ _ hTag'
  (.logical (.reflexive (tupleValue J (args.toList.map (termValue J.ctag J.atag e raw)))))
 obtain ⟨hh⟩ := pairCongruence p J H.hc H.ha _ _ _ _ hArity hp
 simpa only [headerTerm,termValue,pairMap,tupleMap,headerValue,List.Vector.toList_map] using (show Nonempty _ from ⟨hh⟩)

theorem matrixCode {arity ctx : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p J) (r s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.value J.ctag J.atag matrix
   (LiteralNumeralPrefix.numeralCall J.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall J.numeralTag s ::ᵥ nil))
   (aliasCode J r s))) := by
 let raw := LiteralNumeralPrefix.numeralCall J.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall J.numeralTag s ::ᵥ nil
 let e := PrescribedRuntimeSpecialization.runtimeEnvironment 2
 obtain ⟨hh⟩ := header p J H e raw 0 (argumentVariables 2)
 rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues] at hh
 obtain ⟨hl⟩ := CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 5 H.hc H.hc _ _ hh
 obtain ⟨hr⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J H.hc H.ha H.hn e raw
  GorbowSourceRegistryPadding.functionTag (GorbowNamedDefiningTheory.headerVariables (2,0) ::ᵥ nil)
 obtain ⟨hcall⟩ := CurrentRecursionProducerCore.CallRawCopy.call p J J H H (Term.numeral GorbowSourceRegistryPadding.functionTag)
  ((GorbowNamedDefiningTheory.headerVariables (2,0) ::ᵥ nil).map (termValue J.ctag J.atag e raw))
  (headerCode J r s ::ᵥ nil) (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact hh)
 exact CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 0 H.hc H.ha H.hc H.ha
  _ _ _ _ hl (Logic.trans _ _ _ hr hcall)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.EncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.EncodingProof
