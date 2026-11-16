module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.RawEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.QuoteProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution
theorem quote {n ctx : Nat} (p : Program n) (old ar : Program 1) (x : Program 3)
 (I : ArithmeticTemplateEvaluation.Installation p old ar x)
 (J : ArithmeticTemplateEvaluation.TemplateInstallation p template)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (hn : K.numeralTag = I.numeralTag) (r s : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call J.quoteTag (r ::ᵥ s ::ᵥ nil)) (CurrentNamedAliasCertificate.headerCode K r s))) := by
 let v := r ::ᵥ s ::ᵥ nil
 let K0 : PrescribedRuntimeCallCongruence.Tags := { K with ctag := I.consTag, atag := I.appendTag }
 have H0 : CurrentRecursionProducerCore.CodecBridge.Nodes p K0 :=
  ⟨I.hc,I.ha,by simpa only [K0,hn] using I.hnumeral⟩
 obtain ⟨hq⟩ := ArithmeticTemplateEvaluation.SymbolicProof.quoteComputes template TemplateProof.arithmetic p old ar x I v J.quoteTag J.hquote
 obtain ⟨hr⟩ := RawEncodingProof.rawValue p K0 H0 template TemplateProof.arithmetic v
 have hr' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (ArithmeticTemplateEvaluation.SymbolicProof.raw I.numeralTag I.consTag I.appendTag v template)
   (termValue I.consTag I.appendTag (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
    (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) template)) := by
  simpa only [K0,hn] using hr
 obtain ⟨hc⟩ := CurrentCompositionCertificate.TermCopiesProof.term p I.consTag I.appendTag K.ctag K.atag
  I.hc I.ha H.hc H.ha (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
  (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) template
 obtain ⟨hh⟩ := CurrentNamedAliasCertificate.EncodingProof.header p K H
  (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
  (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) 0 (GorbowPRDefiningEquations.argumentVariables 2)
 rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues] at hh
 have hh' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
   (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) template)
   (CurrentNamedAliasCertificate.headerCode K r s)) := by
  simpa only [template,GorbowNamedDefiningTheory.headerVariables,v,List.Vector.map_cons,List.Vector.map_nil,
   CurrentNamedAliasCertificate.headerCode,Term.numeral] using hh
 exact ⟨Logic.trans _ _ _ hq.finish (Logic.trans _ _ _ hr' (Logic.trans _ _ _ hc hh'))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.QuoteProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.QuoteProof
