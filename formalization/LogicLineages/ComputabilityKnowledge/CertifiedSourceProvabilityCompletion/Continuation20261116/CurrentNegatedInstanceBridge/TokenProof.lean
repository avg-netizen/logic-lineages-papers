module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InstanceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.TokenProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport
def tasks {n ctx : Nat} {p : Program n} (I : UniformClosedRule13Validity.Installation p) : Term ctx :=
 LiteralSyntaxValidator.FormulaBindingProof.taskList I.ptag I.ctag (.succ .zero)
def tokenPrefix {n ctx : Nat} {p : Program n} (I : UniformClosedRule13Validity.Installation p) : Term ctx :=
 HistoryLookup.consCall I.ctag (Term.numeral 6) .zero

theorem step {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxStep.stepCall I.stepTag (.succ (tasks I : Term ctx)) (Term.numeral 6)) (.succ (tasks I)))) := by
 obtain ⟨etag,he⟩ := LiteralSyntaxFrame.StepCases.expandInstalled p I.stepTag I.h_stepTag
 obtain ⟨hs⟩ := ConstructorStepProof.stepAt p I.stepTag etag I.ptag I.ctag I.atag
  I.h_stepTag he I.h_ptag I.h_ctag I.h_atag (.formula 6) (.succ .zero : Term ctx) .zero
 obtain ⟨ha⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.singletonAppendNil p I.atag I.ctag
  I.h_atag I.h_ctag (LiteralSyntaxStep.taskCall I.ptag 1 (.succ .zero : Term ctx))
 exact ⟨Logic.trans _ _ _ hs (Logic.unary (.succ (.var 0)) _ _ ha)⟩

theorem emit {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionEmit.emitCall I.etag (.succ (tasks I)) (Term.numeral 6) raw) (tokenPrefix I))) :=
 UniformSubstitutionChunkTransport.EmitterProof.formula p I.etag I.ptag I.ctag
  I.h_etag I.h_ptag I.h_ctag (.succ .zero) .zero (Term.numeral 6) raw

theorem appendPrefix {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p) (a : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall I.atag (tokenPrefix I) a) (negValue I.ctag a))) := by
 obtain ⟨hc⟩ := HistoryAppend.ConsProof.internalAppendCons n p I.atag I.ctag I.h_atag I.h_ctag ctx (Term.numeral 6) .zero a
 obtain ⟨hz⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p I.atag I.h_atag ctx a
 exact ⟨Logic.trans _ _ _ hc (UniformClosedRule13Validity.GraphProof.binaryCongruence I.ctag
  (Term.numeral 6) _ (Term.numeral 6) a (.logical (.reflexive _)) hz)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.TokenProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.TokenProof
