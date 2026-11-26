module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnarySourceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivitySourceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.StatementChecks
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem exactTraces : Targets.InternalTraces := by
 intro installed lhs rhs k t old a baseX pF pR I ctx P f left middle right htu huv
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 obtain ⟨hu⟩ := UnaryTraceProof.trace (ctx := ctx) p installed lhs rhs t old a _ I f left middle
 obtain ⟨ht⟩ := TransitivityTraceProof.trace (ctx := ctx) p installed lhs rhs t old a _ I P left middle right htu huv
 exact CumulativePropositionalSource.CapabilitySupport.inSource installed lhs rhs pF pR old a baseX _
  ⟨Derivation.mp (.mp (.logical (.andIntro _ _)) hu) ht⟩
theorem exactUnaryRule : Targets.InternalUnaryRule := UnarySourceProof.exactUnaryRule
theorem exactTransitivityUnder : Targets.InternalTransitivityUnder := TransitivitySourceProof.exactTransitivityUnder
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.StatementChecks
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.StatementChecks
