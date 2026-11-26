module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
def template (a b : Term 1) : Formula 1 := .equal a b
def templateCode (a b : Term 1) : Nat := Encodable.encode (GorbowFormulaPrefixCode.encode (template a b))
def instanceProgram (a b : Term 1) : Program 1 :=
 RawUniversalReplace.binaryRaw 0 (RawUnarySubstitution.program a) (RawUnarySubstitution.program b)
def formulaProgram (a b : Term 1) : Program 1 :=
 RawUniversalReplace.binaryRaw 7
  (applyTwo HistoryCodec.cons (constant 1 10) (constant 1 (templateCode a b)))
  (instanceProgram a b)
/-- Original rule0/tag13, exactly [phi,t], both references zero. -/
def line (a b : Term 1) : Program 1 :=
 applyTwo HistoryCodec.pair (constant 1 0)
  (applyTwo HistoryCodec.pair (formulaProgram a b)
   (applyTwo HistoryCodec.pair (constant 1 0)
    (applyTwo HistoryCodec.pair (constant 1 13)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons (constant 1 (templateCode a b))
       (applyTwo HistoryCodec.cons (.projection 0) (constant 1 0)))
      (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0))))))
def nativeLine (a b : Term 1) (u : Term 0) : GorbowProofChecker.Line :=
 (0,GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate (template a b) u)),
  0,13,[GorbowFormulaPrefixCode.encode (template a b),GorbowTermPrefixCode.encode u],0,0)
def instanceValue {ctx : Nat} (ctag atag : Nat) (a b : Term 1) (raw : Term ctx) : Term ctx :=
 RawUniversalReplace.binaryValue ctag atag 0
  (RawUnarySubstitution.value ctag atag raw a) (RawUnarySubstitution.value ctag atag raw b)
def formulaValue {ctx : Nat} (ctag atag : Nat) (a b : Term 1) (raw : Term ctx) : Term ctx :=
 RawUniversalReplace.binaryValue ctag atag 7
  (HistoryLookup.consCall ctag (Term.numeral 10) (Term.numeral (templateCode a b)))
  (instanceValue ctag atag a b raw)
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (a b : Term 1) (raw : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (formulaValue ctag atag a b raw)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 13)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag (Term.numeral (templateCode a b))
       (HistoryLookup.consCall ctag raw .zero))
      (HistoryKernel.pairCall ptag .zero .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiation
