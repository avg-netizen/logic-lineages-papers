module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.PairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
/-- Exactly hs once, hs twice as multiplication inputs, then hm and hac.
This is the original arithmetic pair-term recipe, not a pairing-code shortcut. -/
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (a b c d hac hbd index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag b))
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag c))
 (hd : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag d))
 (hhac : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag a c) hac))
 (hhbd : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag b d) hbd)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel
   (equalValue I.current.ctag I.current.atag (pairValue (tags I) a b) (pairValue (tags I) c d))
   (pairCertificate (tags I) a b c d hac hbd))) := by
 obtain ⟨hs⟩ := ScalarProof.binary p f lhs rhs t old arithmetic x I G false a b c d hac hbd index fuel ha hb hc hd hhac hhbd
 have hsc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 obtain ⟨hsab⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I G false a b ha hb
 obtain ⟨hscd⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I G false c d hc hd
 obtain ⟨hm⟩ := ScalarProof.binary p f lhs rhs t old arithmetic x I G true
  (binaryValue (tags I) false a b) (binaryValue (tags I) false a b)
  (binaryValue (tags I) false c d) (binaryValue (tags I) false c d)
  (binaryCertificate (tags I) false a b c d hac hbd) (binaryCertificate (tags I) false a b c d hac hbd)
  index fuel hsab hsab hscd hscd hsc hsc
 have hmc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hm
 obtain ⟨hmab⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I G true
  (binaryValue (tags I) false a b) (binaryValue (tags I) false a b) hsab hsab
 obtain ⟨hmcd⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I G true
  (binaryValue (tags I) false c d) (binaryValue (tags I) false c d) hscd hscd
 exact ScalarProof.binary p f lhs rhs t old arithmetic x I G false _ a _ c _ hac index fuel hmab ha hmcd hc hmc hhac
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.PairProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.PairProof
