module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem term {arity inputs n depth rawCount ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (f : Term n) (e : FixedFormulaSubstitution.Environment n depth rawCount) (raw : List.Vector (Program inputs) rawCount)
 (values : List.Vector (Term ctx) rawCount) (J : Tags) (I : Installation p J)
 (hr : ∀ i, Computes p (raw.get i) args (values.get i)) :
 Computes p (.composition (FixedFormulaSubstitution.termProgram e f) raw.get) args
  (FixedFormulaSubstitution.termValue J.ctag J.atag e values f) := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag _ raw.get ht args values
  (fun i => hr i _ (Equations.argumentChild p tag _ raw.get ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalTerm n depth rawCount e f arity p (tag+1) J.ctag J.atag
  (Equations.functionChild p tag _ raw.get ht) I.hc I.ha ctx values
 exact ⟨Logic.trans _ _ _ he hf⟩

theorem reflexivity {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (raw : Program inputs) (v : Term ctx) (h : Computes p raw args v) :
 Computes p (CurrentRecursionStepProgram.reflexivity raw) args (reflexivityCertificate J v) :=
 singletonGraph p args J.rctag I.hrc _ _
  (LiteralRawMP.ConstructorSupportProof.unary p args RawReflexivity.lineConstructor J.reflexivityTag I.hr raw v h)

theorem binaryCode {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (opcode : Nat) (a b : Program inputs) (av bv : Term ctx)
 (ha : Computes p a args av) (hb : Computes p b args bv) :
 Computes p (FixedFormulaSubstitution.binary opcode a b) args (FixedFormulaSubstitution.binaryValue J.ctag J.atag opcode av bv) :=
 LiteralRawMP.ConstructorSupportProof.binary p args HistoryCodec.cons J.ctag I.hc _ _ _ _ (constantValue p args opcode)
  (LiteralRawMP.ConstructorSupportProof.binary p args HistoryAppend.append J.atag I.ha a b av bv ha hb)

theorem unaryCode {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (opcode : Nat) (a : Program inputs) (av : Term ctx)
 (ha : Computes p a args av) :
 Computes p (FixedFormulaSubstitution.unary opcode a) args (FixedFormulaSubstitution.unaryValue J.ctag opcode av) :=
 LiteralRawMP.ConstructorSupportProof.binary p args HistoryCodec.cons J.ctag I.hc _ _ _ _ (constantValue p args opcode) ha

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphSupport
