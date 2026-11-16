module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
/-- false: original logical annotation2, classical contraposition.
true: original annotation10, existential duality backward. The latter's
second coordinate is genuinely unused, not an additional formula premise. -/
def conclusion {n : Nat} (isExists : Bool) (a b : Program n) : Program n :=
 if isExists then FixedFormulaSubstitution.binary 7
  (FixedFormulaSubstitution.unary 6 (FixedFormulaSubstitution.unary 10 (FixedFormulaSubstitution.unary 6 a)))
  (FixedFormulaSubstitution.unary 11 a)
 else FixedFormulaSubstitution.binary 7
  (FixedFormulaSubstitution.binary 7 (FixedFormulaSubstitution.unary 6 a) (FixedFormulaSubstitution.unary 6 b))
  (FixedFormulaSubstitution.binary 7 b a)
def arguments {n : Nat} (isExists : Bool) (a b : Program n) : Program n :=
 applyTwo HistoryCodec.cons a (if isExists then constant n 0 else applyTwo HistoryCodec.cons b (constant n 0))
/-- EXACT original seven-field line encoding: context0, conclusion, rule0,
annotation2/10, original argument list, references0/0. -/
def line {n : Nat} (isExists : Bool) (a b : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (conclusion isExists a b)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n (if isExists then 10 else 2))
     (applyTwo HistoryCodec.pair (arguments isExists a b)
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor (isExists : Bool) : Program 2 := line isExists (.projection 0) (.projection 1)
def singletonConstructor (isExists : Bool) : Program 2 :=
 applyTwo HistoryCodec.cons (lineConstructor isExists) (constant 2 0)

def conclusionValue {ctx : Nat} (isExists : Bool) (ctag atag : Nat) (a b : Term ctx) : Term ctx :=
 if isExists then impValue ctag atag
  (FixedFormulaSubstitution.unaryValue ctag 6 (FixedFormulaSubstitution.unaryValue ctag 10 (FixedFormulaSubstitution.unaryValue ctag 6 a)))
  (FixedFormulaSubstitution.unaryValue ctag 11 a)
 else impValue ctag atag
  (impValue ctag atag (FixedFormulaSubstitution.unaryValue ctag 6 a) (FixedFormulaSubstitution.unaryValue ctag 6 b))
  (impValue ctag atag b a)
def argumentsValue {ctx : Nat} (isExists : Bool) (ctag : Nat) (a b : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag a (if isExists then .zero else HistoryLookup.consCall ctag b .zero)
def lineValue {ctx : Nat} (isExists : Bool) (ptag ctag atag : Nat) (a b : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag (conclusionValue isExists ctag atag a b)
  (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag (Term.numeral (if isExists then 10 else 2))
   (HistoryKernel.pairCall ptag (argumentsValue isExists ctag a b) (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx := call tag (a ::ᵥ b ::ᵥ nil)
def singletonValue {ctx : Nat} (lineTag ctag : Nat) (a b : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (lineCall lineTag a b) .zero

structure Installation {arity : Nat} (p : Program arity) (ptag ctag atag : Nat) : Prop where
 hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers
