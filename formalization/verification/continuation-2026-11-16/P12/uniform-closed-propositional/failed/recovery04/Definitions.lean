module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 HistoryRuleSuffix List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- false selects original annotation0(K), true annotation1(S). The unused
third K coordinate never enters its two-element payload or formula. -/
def conclusion {n : Nat} (isS : Bool) (a b c : Program n) : Program n :=
 if isS then FixedFormulaSubstitution.binary 7 (FixedFormulaSubstitution.binary 7 a (FixedFormulaSubstitution.binary 7 b c))
  (FixedFormulaSubstitution.binary 7 (FixedFormulaSubstitution.binary 7 a b) (FixedFormulaSubstitution.binary 7 a c))
 else FixedFormulaSubstitution.binary 7 a (FixedFormulaSubstitution.binary 7 b a)
def arguments {n : Nat} (isS : Bool) (a b c : Program n) : Program n :=
 applyTwo HistoryCodec.cons a (applyTwo HistoryCodec.cons b
  (if isS then applyTwo HistoryCodec.cons c (constant n 0) else constant n 0))
def line {n : Nat} (isS : Bool) (a b c : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (conclusion isS a b c)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n (if isS then 1 else 0))
     (applyTwo HistoryCodec.pair (arguments isS a b c)
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor (isS : Bool) : Program 3 := line isS (.projection 0) (.projection 1) (.projection 2)
def firstArg : Program 1 := TwoSol20261113.ReflexivityRecognizer.termCode
def secondArg : Program 1 := Continuation20261114.RawAddSucc.secondTermCode
def thirdArg : Program 1 := UniformClosedRule12.thirdTermCode
def formulaGuard {n : Nat} (a : Program n) : Program n :=
 applyTwo LiteralSyntaxValidator.formulaValidator (constant n 0) a
def recognizer (isS : Bool) : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (line isS firstArg secondArg thirdArg))
 (conjunction (formulaGuard firstArg)
  (if isS then conjunction (formulaGuard secondArg) (formulaGuard thirdArg) else formulaGuard secondArg))
/-- Conservative literal fallback; no claim about any pre-existing arbitrary I. -/
def logicalLeaf (old : Program 1) : Program 1 :=
 choose (recognizer true) (choose (recognizer false) old (constant 1 1)) (constant 1 1)
def nativeConclusion (isS : Bool) (a b c : List Nat) : List Nat :=
 if isS then GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 7 a (GorbowCodeConstructors.binary 7 b c))
  (GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 7 a b) (GorbowCodeConstructors.binary 7 a c))
 else GorbowCodeConstructors.binary 7 a (GorbowCodeConstructors.binary 7 b a)
def nativeLine (isS : Bool) (a b c : List Nat) : GorbowProofChecker.Line :=
 (0,nativeConclusion isS a b c,0,(if isS then 1 else 0),(if isS then [a,b,c] else [a,b]),0,0)
def conclusionValue {ctx : Nat} (isS : Bool) (ctag atag : Nat) (a b c : Term ctx) : Term ctx :=
 if isS then PrescribedRuntimeEquality.impValue ctag atag (PrescribedRuntimeEquality.impValue ctag atag a (PrescribedRuntimeEquality.impValue ctag atag b c))
  (PrescribedRuntimeEquality.impValue ctag atag (PrescribedRuntimeEquality.impValue ctag atag a b) (PrescribedRuntimeEquality.impValue ctag atag a c))
 else PrescribedRuntimeEquality.impValue ctag atag a (PrescribedRuntimeEquality.impValue ctag atag b a)
def argumentsValue {ctx : Nat} (isS : Bool) (ctag : Nat) (a b c : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag a (HistoryLookup.consCall ctag b
  (if isS then HistoryLookup.consCall ctag c .zero else .zero))
def lineValue {ctx : Nat} (isS : Bool) (ptag ctag atag : Nat) (a b c : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag (conclusionValue isS ctag atag a b c)
  (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag (Term.numeral (if isS then 1 else 0))
   (HistoryKernel.pairCall ptag (argumentsValue isS ctag a b c) (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (qtag : Nat) (a b c : Term ctx) : Term ctx := call qtag (a ::ᵥ b ::ᵥ c ::ᵥ nil)
def formulaValid {ctx : Nat} (fval : Nat) (a : Term ctx) : Formula ctx :=
 .equal (LiteralSyntaxValidator.formulaCall fval .zero a) (.succ .zero)
def guards {ctx : Nat} (isS : Bool) (fval : Nat) (a b c : Term ctx) : Formula ctx :=
 .conj (formulaValid fval a) (if isS then .conj (formulaValid fval b) (formulaValid fval c) else formulaValid fval b)
/-- Literal original singleton recipe used by HasCertificates.k/s. -/
def singletonNumber (isS : Bool) (a b c : Formula 0) : Nat :=
 GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (if isS then .s a b c else .k a b)]
def singletonValue {ctx : Nat} (qtag ctag : Nat) (a b c : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (lineCall qtag a b c) .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional
