module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- One fixed original full unary formula, permitting nested quantifiers and
all nonarithmetical symbols. Its AST is fixed before every raw runtime input. -/
def environment : FixedFormulaSubstitution.Environment 1 0 1 := fun _ => .inr 0
def templateCode (f : Formula 1) : Nat := Encodable.encode (GorbowFormulaPrefixCode.encode f)
def instanceProgram (f : Formula 1) : Program 1 :=
 FixedFormulaSubstitution.formulaProgram f environment
def formulaProgram (f : Formula 1) : Program 1 :=
 RawUniversalReplace.binaryRaw 7
  (applyTwo HistoryCodec.cons (constant 1 10) (constant 1 (templateCode f)))
  (instanceProgram f)
/-- Original rule0/tag13, exactly [phi,t], both references zero. -/
def line (f : Formula 1) : Program 1 :=
 applyTwo HistoryCodec.pair (constant 1 0)
  (applyTwo HistoryCodec.pair (formulaProgram f)
   (applyTwo HistoryCodec.pair (constant 1 0)
    (applyTwo HistoryCodec.pair (constant 1 13)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons (constant 1 (templateCode f))
       (applyTwo HistoryCodec.cons (.projection 0) (constant 1 0)))
      (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0))))))
def nativeLine (f : Formula 1) (u : Term 0) : GorbowProofChecker.Line :=
 (0,GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate f u)),
  0,13,[GorbowFormulaPrefixCode.encode f,GorbowTermPrefixCode.encode u],0,0)
def instanceValue {ctx : Nat} (ctag atag : Nat) (f : Formula 1) (raw : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.formulaValue ctag atag (raw ::ᵥ nil) f environment
def formulaValue {ctx : Nat} (ctag atag : Nat) (f : Formula 1) (raw : Term ctx) : Term ctx :=
 RawUniversalReplace.binaryValue ctag atag 7
  (HistoryLookup.consCall ctag (Term.numeral 10) (Term.numeral (templateCode f)))
  (instanceValue ctag atag f raw)
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (f : Formula 1) (raw : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (formulaValue ctag atag f raw)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 13)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag (Term.numeral (templateCode f))
       (HistoryLookup.consCall ctag raw .zero))
      (HistoryKernel.pairCall ptag .zero .zero)))))
/-- Original second annotation field in [phi,u]. -/
def argumentCode : Program 1 := RawAddSucc.secondTermCode
def recognizer (f : Formula 1) : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (applyOne (line f) argumentCode))
 (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator argumentCode)
def logicalLeaf (f : Formula 1) (old : Program 1) : Program 1 :=
 choose (recognizer f) old (constant 1 1)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation
