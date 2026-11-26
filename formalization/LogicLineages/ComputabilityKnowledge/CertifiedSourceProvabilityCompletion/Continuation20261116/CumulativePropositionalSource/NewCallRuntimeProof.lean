module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallTupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem exactTupleAndCall : CallAlgebraTargets.InternalTupleAndCall := by
 intro arity k p f lhs rhs t old arithmetic x I ctx G n tag index fuel args others codes ha hb hh
 let J := tags I.previous
 let tagRaw := LiteralNumeralPrefix.numeralCall J.numeralTag tag
 let arityRaw : Term ctx := rawNumeral (Term.numeral n)
 let A := tupleValue J args.toList
 let B := tupleValue J others.toList
 obtain ⟨ht⟩ := NewCallTupleProof.current p f lhs rhs t old arithmetic x I G index fuel n args others codes ha hb hh
 have htc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ht
 obtain ⟨hva⟩ := TupleValidityProof.current p f lhs rhs t old arithmetic x I.previous G n args ha
 obtain ⟨hvb⟩ := TupleValidityProof.current p f lhs rhs t old arithmetic x I.previous G n others hb
 obtain ⟨hvt⟩ := ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag I.previous.previous.previous.previous.previous.hnumeral G tag
 obtain ⟨hvn⟩ := ValidityProof.closed p _ _ _ I.previous.current G (Term.numeral n)
 obtain ⟨hrt⟩ := NewCallReflexivityProof.current p f lhs rhs t old arithmetic x I G tagRaw index fuel hvt
 obtain ⟨hrn⟩ := NewCallReflexivityProof.current p f lhs rhs t old arithmetic x I G arityRaw index fuel hvn
 have hrtc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrt
 have hrnc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrn
 obtain ⟨hp⟩ := NewCallPairProof.current p f lhs rhs t old arithmetic x I G tagRaw A tagRaw B
  (reflexivityCertificate J tagRaw) (tupleCertificate J args others codes) index fuel hvt hva hvt hvb hrtc htc
 have hpc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hp
 obtain ⟨hvpa⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I.previous G tagRaw A hvt hva
 obtain ⟨hvpb⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I.previous G tagRaw B hvt hvb
 obtain ⟨hheader⟩ := NewCallPairProof.current p f lhs rhs t old arithmetic x I G arityRaw (pairValue J tagRaw A)
  arityRaw (pairValue J tagRaw B) (reflexivityCertificate J arityRaw)
  (pairCertificate J tagRaw A tagRaw B (reflexivityCertificate J tagRaw) (tupleCertificate J args others codes))
  index fuel hvn hvpa hvn hvpb hrnc hpc
 have hhc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hheader
 obtain ⟨hvha⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I.previous G arityRaw (pairValue J tagRaw A) hvn hvpa
 obtain ⟨hvhb⟩ := ConstructorValidityProof.pair p f lhs rhs t old arithmetic x I.previous G arityRaw (pairValue J tagRaw B) hvn hvpb
 obtain ⟨hcall⟩ := NewCallScalarProof.unary p f lhs rhs t old arithmetic x I G true
  (headerValue J tag args) (headerValue J tag others)
  (pairCertificate J arityRaw (pairValue J tagRaw A) arityRaw (pairValue J tagRaw B)
   (reflexivityCertificate J arityRaw)
   (pairCertificate J tagRaw A tagRaw B (reflexivityCertificate J tagRaw) (tupleCertificate J args others codes)))
  index fuel hvha hvhb hhc
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) ht) hcall⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
