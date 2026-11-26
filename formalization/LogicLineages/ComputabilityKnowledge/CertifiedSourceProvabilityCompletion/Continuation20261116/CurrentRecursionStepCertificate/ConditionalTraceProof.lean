module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConditionalTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open PrescribedRuntimeCallCongruence

theorem trace {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (tTemplate : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs tTemplate old a x)
 (pF left middle right htu huv : Term ctx) (P : Formula 0) (t u v : Term 0) (ntu nuv : Nat)
 (hp : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal pF (formulaNumeral P)))
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal left (rawNumeral t)))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal middle (rawNumeral u)))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal right (rawNumeral v)))
 (hleftCode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal htu (Term.numeral ntu)))
 (hrightCode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal huv (Term.numeral nuv))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transitivityUnderCertificate I pF left middle right htu huv)
   (Term.numeral (transitivityUnderNumber P t u v ntu nuv)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let J := tags I.previous
 have hc := I.previous.current.h_ctag
 have ha := I.previous.current.h_atag
 let matrix := equalValue J.ctag J.atag left
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 let tu := equalValue J.ctag J.atag left middle
 let tv := equalValue J.ctag J.atag left right
 let uv := equalValue J.ctag J.atag middle right
 have htlift : Derivation T (.equal left
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 t))))) := by
  rw [EncodingProof.liftEncode]
  exact ht
 obtain ⟨hmat⟩ := EncodingProof.equal p J.ctag J.atag hc ha left _
  (GorbowClosedEquality.liftClosedTerm 1 t) (.var (0 : Fin 1)) htlift (.logical (.reflexive _))
 obtain ⟨hseed⟩ := TracePrimitives.replacement p T (fun _ h => h) J.ctag J.constructorTag hc I.previous.current.h_constructor
  matrix middle right (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v hmat hu hv
 obtain ⟨htuEq⟩ := EncodingProof.equal p J.ctag J.atag hc ha left middle t u ht hu
 obtain ⟨htvEq⟩ := EncodingProof.equal p J.ctag J.atag hc ha left right t v ht hv
 obtain ⟨huvEq⟩ := EncodingProof.equal p J.ctag J.atag hc ha middle right u v hu hv
 obtain ⟨hinner⟩ := EncodingProof.imp p J.ctag J.atag hc ha tu tv (.equal t u) (.equal t v) htuEq htvEq
 obtain ⟨houter⟩ := EncodingProof.imp p J.ctag J.atag hc ha uv (impValue J.ctag J.atag tu tv)
  (.equal u v) (.imp (.equal t u) (.equal t v)) huvEq hinner
 obtain ⟨hlift⟩ := TraceOperations.lift p T (fun _ h => h) installed lhs rhs tTemplate old a x I
  (impValue J.ctag J.atag uv (impValue J.ctag J.atag tu tv)) pF _
  (.imp (.equal u v) (.imp (.equal t u) (.equal t v))) P _ houter hp hseed
 obtain ⟨hfirst⟩ := TraceOperations.mpUnder p T (fun _ h => h) installed lhs rhs tTemplate old a x I
  pF uv (impValue J.ctag J.atag tu tv) _ huv P (.equal u v) (.imp (.equal t u) (.equal t v)) _ nuv
  hp huvEq hinner hlift hrightCode
 exact TraceOperations.mpUnder p T (fun _ h => h) installed lhs rhs tTemplate old a x I
  pF tu tv _ htu P (.equal t u) (.equal t v) _ ntu hp htuEq htvEq hfirst hleftCode
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConditionalTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConditionalTraceProof
