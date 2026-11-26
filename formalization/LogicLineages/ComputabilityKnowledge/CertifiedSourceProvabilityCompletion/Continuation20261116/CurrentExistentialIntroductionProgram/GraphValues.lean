module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphInterface
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphValues
open GorbowSyntax GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GraphInterface
abbrev nv {ctx : Nat} (J : Tags) (a : Term ctx) := FixedFormulaSubstitution.unaryValue J.ctag 6 a
abbrev iv {ctx : Nat} (J : Tags) (a b : Term ctx) := PrescribedRuntimeEquality.impValue J.ctag J.atag a b
abbrev cc {ctx : Nat} (J : Tags) (a b : Term ctx) := OriginalQuantifierLogicalProducers.lineCall J.contraTag a b
def dneValue {ctx : Nat} (J : Tags) (p : Term ctx) : Term ctx :=
 let R := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.equal .zero .zero : Formula 0)))
 let A := nv J (nv J p)
 let c1 := cc J (nv J R) (nv J p)
 let k := UniformClosedPropositionalCertificate.certificate J.ctag J.ktag A (nv J (nv J R)) A
 let first := composeValue J A (iv J (nv J (nv J R)) A) (iv J (nv J p) (nv J R)) c1 k
 let c2 := cc J p R
 let second := composeValue J A (iv J (nv J p) (nv J R)) (iv J R p) c2 first
 let truth := RawCumulativeLogical.certificate J.ctag J.reflexivityTag
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (Term.zero : Term 0))))
 mpUnderValue J A R p second (liftValue J R A truth)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphValues
