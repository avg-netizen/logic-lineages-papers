module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.TransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CompletionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open SymbolicProof

theorem internalEvaluation : Targets.InternalEvaluation := by
 intro k t ha n p old a x I J ctx values index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let rt := raw I.numeralTag I.consTag I.appendTag values t
 let answer := LiteralNumeralPrefix.numeralCall I.numeralTag (instantiatedValue t values)
 let cert := certificate I values t
 obtain ⟨hh⟩ := CoreProof.symbolicEvaluation t ha p old a x I values index fuel
 have hv := GorbowTheoryProof.Derivation.mp (.logical (.andLeft _ _)) hh
 have hc := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) hh
 obtain ⟨hquoteLocal⟩ := quoteComputes t ha p old a x I values J.quoteTag J.hquote
 have hquote := Hilbert.Local.finish hquoteLocal
 obtain ⟨hcertLocal⟩ := certificateComputes t ha p old a x I values J.certificateTag J.hcertificate
 have hcert := Hilbert.Local.finish hcertLocal
 have hvq := HistoryLookup.DestructorProof.unaryCallCongruence (T := T) I.validatorTag _ _ hquote
 have hvfinal := Logic.trans _ _ _ hvq hv
 have hm := TransportProof.moveLeft (T := T) I.qctag I.consTag I.appendTag index fuel rt answer cert (call J.quoteTag values)
 have hcq := GorbowTheoryProof.Derivation.mp (.mp hm (Support.equalitySymmetry _ _ hquote)) hc
 have hmc := TransportProof.moveCertificate (T := T) I.qctag I.consTag I.appendTag index fuel (call J.quoteTag values) answer cert (call J.certificateTag values)
 have hfinal := GorbowTheoryProof.Derivation.mp (.mp hmc (Support.equalitySymmetry _ _ hcert)) hcq
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hvfinal) hfinal⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CompletionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CompletionProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CompletionProof.internalEvaluation
