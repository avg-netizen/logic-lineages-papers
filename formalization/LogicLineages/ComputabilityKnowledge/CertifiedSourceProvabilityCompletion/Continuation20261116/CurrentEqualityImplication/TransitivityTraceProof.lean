module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TraceOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem trace {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (tTemplate : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs tTemplate old a x) (P : Formula 0) (t u v : Term 0) (htu huv : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transitivityUnderCertificate I (formulaNumeral P) (rawNumeral (ctx := ctx) t)
   (rawNumeral u) (rawNumeral v) (Term.numeral htu) (Term.numeral huv))
   (Term.numeral (transitivityUnderNumber P t u v htu huv)))) := by
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 have hc := I.previous.current.h_ctag
 have ha := I.previous.current.h_atag
 have hq := I.previous.current.h_constructor
 let T := GorbowPRNumeralCalculation.Theory p
 let matrix := equalValue J.ctag J.atag (rawNumeral (ctx := ctx) t)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let tu := equalValue J.ctag J.atag (rawNumeral (ctx := ctx) t) (rawNumeral u)
 let tv := equalValue J.ctag J.atag (rawNumeral (ctx := ctx) t) (rawNumeral v)
 have ht : Derivation T (.equal (rawNumeral (ctx := ctx) t)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 t))))) := by
  rw [EncodingProof.liftEncode]
  exact .logical (.reflexive _)
 obtain ⟨hmat⟩ := EncodingProof.equal (ctx := ctx) p J.ctag J.atag hc ha _ _
  (GorbowClosedEquality.liftClosedTerm 1 t) (.var (0 : Fin 1)) ht (.logical (.reflexive _))
 obtain ⟨hseed⟩ := TraceGraphProof.replacement p J.ctag J.constructorTag hc hq matrix
  (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v hmat
 obtain ⟨htuEq⟩ := EncodingProof.equal (ctx := ctx) p J.ctag J.atag hc ha (rawNumeral t) (rawNumeral u) t u
  (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨htvEq⟩ := EncodingProof.equal (ctx := ctx) p J.ctag J.atag hc ha (rawNumeral t) (rawNumeral v) t v
  (.logical (.reflexive _)) (.logical (.reflexive _))
 let uv := equalValue J.ctag J.atag (rawNumeral (ctx := ctx) u) (rawNumeral v)
 obtain ⟨huvEq⟩ := EncodingProof.equal (ctx := ctx) p J.ctag J.atag hc ha (rawNumeral u) (rawNumeral v) u v
  (.logical (.reflexive _)) (.logical (.reflexive _))
 obtain ⟨hinner⟩ := EncodingProof.imp p J.ctag J.atag hc ha tu tv (.equal t u) (.equal t v) htuEq htvEq
 obtain ⟨houter⟩ := EncodingProof.imp p J.ctag J.atag hc ha uv (impValue J.ctag J.atag tu tv)
  (.equal u v) (.imp (.equal t u) (.equal t v)) huvEq hinner
 obtain ⟨hlift⟩ := TraceOperations.lift p installed lhs rhs tTemplate old a x I
  (impValue J.ctag J.atag uv (impValue J.ctag J.atag tu tv)) (formulaNumeral P) _
  (.imp (.equal u v) (.imp (.equal t u) (.equal t v))) P _ houter (.logical (.reflexive _)) hseed
 obtain ⟨hfirst⟩ := TraceOperations.mpUnder p installed lhs rhs tTemplate old a x I
  (formulaNumeral P) uv (impValue J.ctag J.atag tu tv) _ (Term.numeral huv)
  P (.equal u v) (.imp (.equal t u) (.equal t v)) _ huv
  (.logical (.reflexive _)) huvEq hinner hlift (.logical (.reflexive _))
 exact TraceOperations.mpUnder p installed lhs rhs tTemplate old a x I
  (formulaNumeral P) tu tv _ (Term.numeral htu) P (.equal t u) (.equal t v) _ htu
  (.logical (.reflexive _)) htuEq htvEq hfirst (.logical (.reflexive _))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityTraceProof
