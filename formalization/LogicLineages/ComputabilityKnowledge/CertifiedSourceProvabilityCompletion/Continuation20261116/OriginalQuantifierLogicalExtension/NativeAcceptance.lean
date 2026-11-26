module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeAcceptance
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open HistoryRuleSuffix.NativeProof OriginalQuantifierLogicalProducers.NativeSupport

theorem rawAccepted (isExists : Bool) (a b : List Nat)
 (h : if isExists then GorbowSyntaxValidation.validFormula 1 a = true
  else GorbowSyntaxValidation.validFormula 0 a = true ∧ GorbowSyntaxValidation.validFormula 0 b = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (nativeLine isExists a b) ::ᵥ nil) = 1 := by
 cases isExists <;>
  simp_all [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
   HistoryDispatcher.truth,GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
   GorbowProofChecker.rule,GorbowProofChecker.payload,nativeLine,nativeConclusion,
   GorbowLogicalAxiomCode.compile,GorbowLogicalAxiomCode.case2,GorbowLogicalAxiomCode.case10,
   GorbowLogicalAxiomCode.guardFormulas,GorbowLogicalAxiomCode.arg]

theorem validOfNonzero {n : Nat} (arity : Nat) (f : Program n) (v : List.Vector Nat n) (a : List Nat)
 (ha : evaluate f v = Encodable.encode a) (h : evaluate (formulaGuard arity f) v ≠ 0) :
 GorbowSyntaxValidation.validFormula arity a = true := by
 have he : evaluate (formulaGuard arity f) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula arity a) := by
  rw [formulaGuard,twoEval,constantEval,ha,LiteralSyntaxValidator.NativeProof.formulaEncoded]
 rw [he] at h
 cases hh : GorbowSyntaxValidation.validFormula arity a with
 | false => exact False.elim (h (by rw [hh]; rfl))
 | true => rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeAcceptance
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.NativeAcceptance
