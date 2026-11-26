module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.NativeProof
open GorbowSyntax GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof

theorem nativeCalibration : Targets.NativeCalibration := by
 intro k t values
 rw [annotationQuote,twoEval,constantEval,twoEval,
  LiteralTemplateQuote.NativeProof.nativeCalibration,constantEval,
  HistoryCodec.NativeProof.nativeConsAllVectors,HistoryCodec.NativeProof.nativePair]
 rfl

/-- External native decoder/compiler success for the ORIGINAL annotation.
This is not an internal logical-leaf equation or certificate acceptance law. -/
theorem nativeCompilation (k : Nat) (t : Term k) (values : List.Vector Nat k) :
 (Encodable.decode (α := GorbowLogicalAxiomCode.Annotation)
   (evaluate (annotationQuote t) values)).bind (GorbowLogicalAxiomCode.compile 0) =
 some (GorbowFormulaPrefixCode.encode (.equal
  (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) t)
  (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) t))) := by
 rw [nativeCalibration,Encodable.encodek,Option.bind_some]
 exact (GorbowLogicalAxiomCodeProof.exactCompilation 0 _ _).mpr
  ⟨.reflexive (GorbowSubstitution.substitute (fun i => (Term.numeral (values.get i) : Term 0)) t),rfl,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralReflexivityQuote.NativeProof
