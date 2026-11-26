module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate

/-- Exact original unaryCongruenceRule: replacement singleton and K-lifted
reflexivity are combined by the original S/two-MP mpUnder. No t=u certificate
is consumed or presumed accepted when synthesizing this ordinary implication. -/
def unaryRuleNumber (f : Term 1) (t u : Term 0) : Nat :=
 let ft := GorbowClosedEquality.instantiateTerm f t
 let fu := GorbowClosedEquality.instantiateTerm f u
 let P := Formula.equal t u
 let Q := Formula.equal ft ft
 let R := Formula.equal ft fu
 mpUnderNumber P Q R
  (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 ft) f) t u)
  (liftNumber Q P (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive ft)]))
/-- Exact original transitivityUnder: lift replacement, mpUnder with the
right-hand input first, then mpUnder with the left-hand input. -/
def transitivityUnderNumber (P : Formula 0) (t u v : Term 0) (htu huv : Nat) : Nat :=
 let TU := Formula.equal t u
 let UV := Formula.equal u v
 let TV := Formula.equal t v
 let seed := replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v
 let first := mpUnderNumber P UV (.imp TU TV) (liftNumber (.imp UV (.imp TU TV)) P seed) huv
 mpUnderNumber P TU TV first htu

def unaryRuleCertificate {arity k n inputs ctx : Nat} {p : Program arity} {installed : Formula 1}
 {lhs rhs : Term 1} {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (raw : List.Vector (Term ctx) inputs) (left right : Term ctx) : Term ctx :=
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 let ft := specializedValue J.ctag J.atag e f raw left
 let fu := specializedValue J.ctag J.atag e f raw right
 let P := equalValue J.ctag J.atag left right
 let Q := equalValue J.ctag J.atag ft ft
 let R := equalValue J.ctag J.atag ft fu
 let matrix := equalValue J.ctag J.atag ft (FixedFormulaSubstitution.termValue J.ctag J.atag e raw f)
 let seed := UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix left right
 let reflexive := RawCumulativeLogical.certificate J.rctag J.reflexivityTag ft
 mpUnderCertificate I P Q R seed (liftCertificate I Q P reflexive)

def transitivityUnderCertificate {arity k ctx : Nat} {p : Program arity} {installed : Formula 1}
 {lhs rhs : Term 1} {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (P left middle right hleft hright : Term ctx) : Term ctx :=
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 let TU := equalValue J.ctag J.atag left middle
 let UV := equalValue J.ctag J.atag middle right
 let TV := equalValue J.ctag J.atag left right
 let matrix := equalValue J.ctag J.atag left
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let seed := UniformClosedRule12Certificate.certificate J.ctag J.constructorTag matrix middle right
 let first := mpUnderCertificate I P UV (impValue J.ctag J.atag TU TV)
  (liftCertificate I (impValue J.ctag J.atag UV (impValue J.ctag J.atag TU TV)) P seed) hright
 mpUnderCertificate I P TU TV first hleft
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication
