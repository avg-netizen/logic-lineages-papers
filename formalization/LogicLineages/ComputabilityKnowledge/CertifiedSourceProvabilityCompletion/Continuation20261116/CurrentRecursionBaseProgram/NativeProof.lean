module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedNativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityNativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeInputs
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution PrescribedRuntimeEquality

theorem exactNative : Targets.NativeBase := by
 intro m base child target inputs
 have hparent := (NativeInputs.parentChild m target inputs).1
 have hchild := (NativeInputs.parentChild m target inputs).2
 have hresult : evaluate (HistoryRuleSuffix.applyOne LiteralNumeralPrefix.numeralCode
  (CurrentCalculationFormulaProgram.tailProgram base)) (target ::ᵥ inputs) =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (evaluate base inputs) : Term 0)) := by
  rw [oneEval,CurrentCalculationFormulaProgram.NativeProof.tailEval,LiteralNumeralPrefix.StatementChecks.exactNative]
 unfold program
 rw [TransitivityNativeProof.transitivityEval _ _ _ _ _ _ _ _ _ hparent hchild hresult]
 rw [SeedNativeProof.seed _ target m _ _ _ (NativeInputs.rootArgumentsEval m target inputs),TagSyntax.root,NativeInputs.childEval]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativeProof
