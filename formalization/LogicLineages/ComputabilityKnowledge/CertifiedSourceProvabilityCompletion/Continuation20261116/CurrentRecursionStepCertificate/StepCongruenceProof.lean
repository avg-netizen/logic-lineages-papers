module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.SymbolicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.StepCongruenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem internal {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (tag : Nat) (G : List (Formula ctx)) (counter left right index fuel : Term ctx) (raw : List.Vector (Term ctx) m)
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag counter))
 (hl : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag left))
 (hr : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag right))
 (hraw : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) :
 let J := tags I.previous
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (impValue J.ctag J.atag (equalValue J.ctag J.atag left right)
    (equalValue J.ctag J.atag (callValue J (Term.numeral tag) (counter ::ᵥ left ::ᵥ raw))
     (callValue J (Term.numeral tag) (counter ::ᵥ right ::ᵥ raw))))
   (unaryRuleCertificate I (stepEnvironment m) (stepTemplate m tag) (counter ::ᵥ raw) left right))) := by
 let J := tags I.previous
 have hin : ∀ i : Fin (m+1), Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((counter ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hc⟩
  | succ i => exact hraw i
 obtain ⟨hu⟩ := CurrentEqualityImplication.UnaryInternalProof.internal p installed lhs rhs t old a x I G
  (stepEnvironment m) (stepTemplate m tag) (counter ::ᵥ raw) left right index fuel hin ⟨hl⟩ ⟨hr⟩
 have huCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hu
 obtain ⟨hleft⟩ := SymbolicProof.stepValue p J I.previous.current.h_ctag I.previous.current.h_atag
  I.previous.previous.previous.previous.previous.hnumeral tag counter left raw
 obtain ⟨hright⟩ := SymbolicProof.stepValue p J I.previous.current.h_ctag I.previous.current.h_atag
  I.previous.previous.previous.previous.previous.hnumeral tag counter right raw
 obtain ⟨heq⟩ := LogicProof.binary (T := GorbowPRNumeralCalculation.Theory p) (G := G) J.ctag J.atag 0 _ _ _ _ (.base hleft) (.base hright)
 obtain ⟨himp⟩ := LogicProof.binary J.ctag J.atag 7 _ _ _ _ (.base (.logical (.reflexive _))) heq
 exact LogicProof.coreFormula I.currentK.coreTag index fuel _ _ _ himp huCore
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.StepCongruenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.StepCongruenceProof
