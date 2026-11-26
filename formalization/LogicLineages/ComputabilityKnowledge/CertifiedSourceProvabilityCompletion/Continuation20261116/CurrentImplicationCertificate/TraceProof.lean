module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.SingletonTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.TraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem exactTraces : Targets.InternalTraces := by
 intro installed lhs rhs k t old a baseX pF pR I ctx A B C code hi ha
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 have hc := I.previous.current.h_ctag
 have hap := I.previous.current.h_atag
 have hm := I.previous.previous.previous.previous.previous.hmp
 obtain ⟨hk⟩ := SingletonTraceProof.singleton p I.currentK.ctag I.currentK.constructorTag false
  I.currentK.h_ctag I.currentK.h_constructorTag A B A (ctx := ctx)
 obtain ⟨hBA⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc hap
  (formulaNumeral (ctx := ctx) B) (formulaNumeral A) B A (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨hlift⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag (formulaNumeral B) (formulaNumeral A))
  (UniformClosedPropositionalCertificate.certificate I.currentK.ctag I.currentK.constructorTag
   (formulaNumeral A) (formulaNumeral B) (formulaNumeral A))
  (Term.numeral code) (.imp B A) (UniformClosedPropositional.singletonNumber false A B A) code
  hBA hk (.logical (.reflexive _))
 obtain ⟨hs⟩ := SingletonTraceProof.singleton p I.currentS.ctag I.currentS.constructorTag true
  I.currentS.h_ctag I.currentS.h_constructorTag A B C (ctx := ctx)
 obtain ⟨hAB⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc hap
  (formulaNumeral (ctx := ctx) A) (formulaNumeral B) A B (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨hAC⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc hap
  (formulaNumeral (ctx := ctx) A) (formulaNumeral C) A C (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨hmiddle⟩ := PrescribedRuntimeEquality.EncodingProof.imp p J.ctag J.atag hc hap
  (impValue J.ctag J.atag (formulaNumeral A) (formulaNumeral B))
  (impValue J.ctag J.atag (formulaNumeral A) (formulaNumeral C)) (.imp A B) (.imp A C) hAB hAC
 obtain ⟨hfirst⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag (impValue J.ctag J.atag (formulaNumeral A) (formulaNumeral B))
   (impValue J.ctag J.atag (formulaNumeral A) (formulaNumeral C)))
  (UniformClosedPropositionalCertificate.certificate I.currentS.ctag I.currentS.constructorTag
   (formulaNumeral A) (formulaNumeral B) (formulaNumeral C))
  (Term.numeral hi) (.imp (.imp A B) (.imp A C)) (UniformClosedPropositional.singletonNumber true A B C) hi
  hmiddle hs (.logical (.reflexive _))
 obtain ⟨hsecond⟩ := PrescribedRuntimeSpecialization.CertificateGraphProof.mp p J.mtag hm
  (impValue J.ctag J.atag (formulaNumeral A) (formulaNumeral C)) _ (Term.numeral ha)
  (.imp A C) _ ha hAC hfirst (.logical (.reflexive _))
 exact CumulativePropositionalSource.CapabilitySupport.inSource installed lhs rhs pF pR old a baseX _
  ⟨Derivation.mp (.mp (.logical (.andIntro _ _)) hlift) hsecond⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.TraceProof
