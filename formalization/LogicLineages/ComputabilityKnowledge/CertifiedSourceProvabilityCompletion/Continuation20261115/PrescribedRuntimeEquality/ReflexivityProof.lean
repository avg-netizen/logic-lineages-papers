module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.ReflexivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LiteralRawMP.DispatcherSupportProof
/-- The same inherited tag11 singleton is retained through every checked CORE
extension. Only actual current-validator success is an input; no reflexive
acceptance, calibration, tag identity or cross-root theory inclusion is assumed. -/
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (raw index fuel : Term ctx)
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag raw raw)
   (RawCumulativeLogical.certificate I.previous.previous.previous.previous.consTag
    I.previous.previous.previous.previous.reflexivityTag raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let J := I.previous.previous.previous.previous
 let A := RawEqualityComposition.eqRaw J.consTag J.appendTag raw raw
 let code := RawCumulativeLogical.certificate J.consTag J.reflexivityTag raw
 obtain ⟨hvcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p J.validatorTag I.current.vtag 1
  TwoSol20261113.ReflexivityRecognizer.termValidator J.hv I.current.h_vtag ctx (raw ::ᵥ nil)
 have holdValid : Hilbert.Local T ctx G (RawReflexivityDispatcher.valid J.validatorTag raw) :=
  localTrans _ _ _ (.base hvcopy) hv
 obtain ⟨hr⟩ := RawUniversalCongruence.ReflexivityProof.internalReflexivity arity p old arithmetic x J ctx raw index fuel
 have hc := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hr) holdValid
 obtain ⟨heq⟩ := EqualityInstantiationCoreRetention.StatementChecks.exactCoreRetention lhs rhs arity p
  LiteralSyntaxValidator.lineValidator (CumulativeInstantiationRegistry.previousLogical old)
  (RawMulNewestAddition.arithmetic arithmetic) x
  J.universalCoreTag I.previous.previous.previous.current.qctag J.pairTag J.consTag J.rightTag J.dropTag
  J.huniversalCore I.previous.previous.previous.current.hqc J.hp J.hc J.hright J.hdrop
  ctx index fuel .zero (.add A A) code
 have hc1 := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) heq) hc
 obtain ⟨hfull⟩ := CumulativeFullFormulaRegistry.CapabilityProof.retention p f lhs rhs t old arithmetic x
  I.previous.previous ctx index fuel .zero (.add A A) code
 have hc2 := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hfull) hc1
 obtain ⟨h13⟩ := CumulativeUniformRule13Registry.CapabilityProof.retention p f lhs rhs t old arithmetic x
  I.previous ctx index fuel .zero (.add A A) code
 have hc3 := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) h13) hc2
 obtain ⟨h12⟩ := CumulativeUniformRule12Registry.CapabilityProof.retention p f lhs rhs t old arithmetic x
  I ctx index fuel .zero (.add A A) code
 have hc4 := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) h12) hc3
 obtain ⟨happend⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p J.appendTag I.current.atag 2
  HistoryAppend.append J.ha I.current.h_atag ctx (raw ::ᵥ raw ::ᵥ nil)
 obtain ⟨hcons⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p J.consTag I.current.ctag 2
  HistoryCodec.cons J.hc I.current.h_ctag ctx
  (Term.numeral 0 ::ᵥ HistoryAppend.appendCall J.appendTag raw raw ::ᵥ nil)
 have hshape := HistoryAppend.PositiveProof.binaryCongruence I.current.ctag
  (Term.numeral (n := ctx) 0) (Term.numeral 0)
  (HistoryAppend.appendCall J.appendTag raw raw) (HistoryAppend.appendCall I.current.atag raw raw)
  (.logical (.reflexive (Term.numeral 0))) happend
 have hAB : Hilbert.Local T ctx G (.equal A (equalValue I.current.ctag I.current.atag raw raw)) :=
  localTrans _ _ _ (.base hcons) (.base hshape)
 exact LogicProof.coreFormula I.current.coreTag index fuel A _ code hAB hc4
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.ReflexivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.ReflexivityProof
