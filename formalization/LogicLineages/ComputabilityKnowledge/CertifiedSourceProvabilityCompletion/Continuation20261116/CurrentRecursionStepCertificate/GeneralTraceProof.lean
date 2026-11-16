module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.GeneralTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internal {arity k n inputs ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (installed : Formula 1) (lhs rhs : Term 1) (tTemplate : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs tTemplate old a x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (template : Term n)
 (raw : List.Vector (Term ctx) inputs) (aF bF : Term ctx) (f : Term 1) (t u : Term 0)
 (ha : Derivation T (.equal aF (rawNumeral t)))
 (hb : Derivation T (.equal bF (rawNumeral u)))
 (hF : Derivation T (.equal (FixedFormulaSubstitution.termValue I.previous.current.ctag I.previous.current.atag e raw template)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode f)))))
 (hft : Derivation T (.equal (specializedValue I.previous.current.ctag I.previous.current.atag e template raw aF)
  (rawNumeral (GorbowClosedEquality.instantiateTerm f t))))
 (hfu : Derivation T (.equal (specializedValue I.previous.current.ctag I.previous.current.atag e template raw bF)
  (rawNumeral (GorbowClosedEquality.instantiateTerm f u)))) :
 Nonempty (Derivation T (.equal (unaryRuleCertificate I e template raw aF bF)
  (Term.numeral (unaryRuleNumber f t u)))) := by
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 let ft := specializedValue J.ctag J.atag e template raw aF
 let fu := specializedValue J.ctag J.atag e template raw bF
 let F := FixedFormulaSubstitution.termValue J.ctag J.atag e raw template
 let matrix := equalValue J.ctag J.atag ft F
 let rr := equalValue J.ctag J.atag ft ft
 let out := equalValue J.ctag J.atag ft fu
 let nt := GorbowClosedEquality.instantiateTerm f t
 let nu := GorbowClosedEquality.instantiateTerm f u
 have hc := I.previous.current.h_ctag
 have hap := I.previous.current.h_atag
 have hftLift : Derivation T (.equal ft
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm 1 nt))))) := by
  rw [EncodingProof.liftEncode]
  exact hft
 obtain ⟨hmat⟩ := TracePrimitives.equal p T hT J.ctag J.atag hc hap ft F (GorbowClosedEquality.liftClosedTerm 1 nt) f hftLift hF
 obtain ⟨hseed⟩ := TracePrimitives.replacement p T hT J.ctag J.constructorTag hc I.previous.current.h_constructor matrix aF bF
  (.equal (GorbowClosedEquality.liftClosedTerm 1 nt) f) t u hmat ha hb
 obtain ⟨hrr⟩ := TracePrimitives.equal p T hT J.ctag J.atag hc hap ft ft nt nt hft hft
 obtain ⟨houtEq⟩ := TracePrimitives.equal p T hT J.ctag J.atag hc hap ft fu nt nu hft hfu
 obtain ⟨hP⟩ := TracePrimitives.equal p T hT J.ctag J.atag hc hap aF bF t u ha hb
 obtain ⟨href⟩ := TracePrimitives.reflexive p T hT J.rctag J.reflexivityTag
  I.previous.previous.previous.previous.previous.hc I.previous.previous.previous.previous.previous.hreflexivity ft nt hft
 obtain ⟨hlift⟩ := TraceOperations.lift p T hT installed lhs rhs tTemplate old a x I rr
  (equalValue J.ctag J.atag aF bF)
  (RawCumulativeLogical.certificate J.rctag J.reflexivityTag ft) (.equal nt nt) (.equal t u) _ hrr hP href
 exact TraceOperations.mpUnder p T hT installed lhs rhs tTemplate old a x I
  (equalValue J.ctag J.atag aF bF) rr out _ _
  (.equal t u) (.equal nt nt) (.equal nt nu) _ _ hP hrr houtEq hseed hlift

theorem exactGeneralUnaryTrace : Targets.GeneralUnaryTrace := by
 intro installed lhs rhs k t old a baseX pF pR I n inputs e template ctx raw aF bF f left right
 dsimp only
 intro ha hb hF hft hfu
 obtain ⟨ha⟩ := ha
 obtain ⟨hb⟩ := hb
 obtain ⟨hF⟩ := hF
 obtain ⟨hft⟩ := hft
 obtain ⟨hfu⟩ := hfu
 exact internal _ _ (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a _ I e template raw aF bF f left right ha hb hF hft hfu
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.GeneralTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.GeneralTraceProof
