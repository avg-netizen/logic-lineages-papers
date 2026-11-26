module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ScalarProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallPairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Exactly hs once, hs twice as multiplication inputs, then hm and hac.
This is the original arithmetic pair-term recipe, not a pairing-code shortcut. -/
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (a b c d hac hbd index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag b))
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag c))
 (hd : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag d))
 (hhac : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag a c) hac))
 (hhbd : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag b d) hbd)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag (pairValue (tags I.previous) a b) (pairValue (tags I.previous) c d))
   (pairCertificate (tags I.previous) a b c d hac hbd))) := by
 obtain ⟨hs⟩ := NewCallScalarProof.binary p f lhs rhs t old arithmetic x I G false a b c d hac hbd index fuel ha hb hc hd hhac hhbd
 have hsc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 obtain ⟨hsab⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G false a b ha hb
 obtain ⟨hscd⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G false c d hc hd
 obtain ⟨hm⟩ := NewCallScalarProof.binary p f lhs rhs t old arithmetic x I G true
  (binaryValue (tags I.previous) false a b) (binaryValue (tags I.previous) false a b)
  (binaryValue (tags I.previous) false c d) (binaryValue (tags I.previous) false c d)
  (binaryCertificate (tags I.previous) false a b c d hac hbd) (binaryCertificate (tags I.previous) false a b c d hac hbd)
  index fuel hsab hsab hscd hscd hsc hsc
 have hmc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hm
 obtain ⟨hmab⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G true
  (binaryValue (tags I.previous) false a b) (binaryValue (tags I.previous) false a b) hsab hsab
 obtain ⟨hmcd⟩ := ConstructorValidityProof.binary p f lhs rhs t old arithmetic x I.previous G true
  (binaryValue (tags I.previous) false c d) (binaryValue (tags I.previous) false c d) hscd hscd
 exact NewCallScalarProof.binary p f lhs rhs t old arithmetic x I G false _ a _ c _ hac index fuel hmab ha hmcd hc hmc hhac
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallPairProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallPairProof
