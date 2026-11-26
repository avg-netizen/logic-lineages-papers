module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.RulesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryInternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem internal {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (tTemplate : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs tTemplate old a x)
 (G : List (Formula ctx)) {n inputs : Nat} (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (raw : List.Vector (Term ctx) inputs) (t u index fuel : Term ctx)
 (hinputs : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i))))
 (ht : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag t)))
 (hu : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag u))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (impValue I.previous.current.ctag I.previous.current.atag
    (equalValue I.previous.current.ctag I.previous.current.atag t u)
    (equalValue I.previous.current.ctag I.previous.current.atag
     (specializedValue I.previous.current.ctag I.previous.current.atag e f raw t)
     (specializedValue I.previous.current.ctag I.previous.current.atag e f raw u)))
   (unaryRuleCertificate I e f raw t u))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue I.previous.current.ctag I.previous.current.atag e f raw t
 let fu := specializedValue I.previous.current.ctag I.previous.current.atag e f raw u
 obtain ⟨ht⟩ := ht
 obtain ⟨hu⟩ := hu
 obtain ⟨hft⟩ := TermGuardProof.specialized p _ _ _ I.previous.current e f G raw t hinputs ht
 have hin : ∀ i : Fin (inputs+1), Nonempty (Hilbert.Local T ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((ft ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hft⟩
  | succ j => exact hinputs j
 obtain ⟨hs⟩ := MatrixProof.certificate p _ _ _ I.previous.current (EnvironmentProof.prepend e)
  (EnvironmentProof.matrix f) G (ft ::ᵥ raw) hin t u index fuel ht hu
 have hs' : Hilbert.Local T ctx G
  (core I.previous.current.coreTag index fuel
   (impValue I.previous.current.ctag I.previous.current.atag (equalValue I.previous.current.ctag I.previous.current.atag t u)
    (impValue I.previous.current.ctag I.previous.current.atag (equalValue I.previous.current.ctag I.previous.current.atag ft ft)
     (equalValue I.previous.current.ctag I.previous.current.atag ft fu)))
   (UniformClosedRule12Certificate.certificate I.previous.current.ctag I.previous.current.constructorTag
    (equalValue I.previous.current.ctag I.previous.current.atag ft (FixedFormulaSubstitution.termValue I.previous.current.ctag I.previous.current.atag e raw f)) t u)) := by
  simpa only [EnvironmentProof.matrixValue,EnvironmentProof.matrixSpecialized,ft,fu] using hs
 obtain ⟨hrr⟩ := ReflexivityProof.current p installed lhs rhs tTemplate old a x I.previous G ft index fuel hft
 obtain ⟨hretain⟩ := CumulativePropositionalSource.CapabilitySupport.retentionInternal p installed lhs rhs tTemplate old a x I index fuel .zero _ _
 have hsNew := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hretain) hs'
 obtain ⟨hretainR⟩ := CumulativePropositionalSource.CapabilitySupport.retentionInternal p installed lhs rhs tTemplate old a x I index fuel .zero _ _
 have hrrNew := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hretainR) hrr
 obtain ⟨hfu⟩ := TermGuardProof.specialized p _ _ _ I.previous.current e f G raw u hinputs hu
 let J := I.previous.current
 let P := equalValue J.ctag J.atag t u
 let Q := equalValue J.ctag J.atag ft ft
 let R := equalValue J.ctag J.atag ft fu
 obtain ⟨hPK⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G false t u ht hu
 obtain ⟨hQK⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G false ft ft hft hft
 obtain ⟨hlift⟩ := RulesProof.lift p installed lhs rhs tTemplate old a x I G Q P _ index fuel ⟨hQK⟩ ⟨hPK⟩ ⟨hrrNew⟩
 have hliftCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hlift
 obtain ⟨hPS⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G true t u ht hu
 obtain ⟨hQS⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G true ft ft hft hft
 obtain ⟨hRS⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G true ft fu hft hfu
 exact RulesProof.mPUnder p installed lhs rhs tTemplate old a x I G P Q R _ _ index fuel
  ⟨hPS⟩ ⟨hQS⟩ ⟨hRS⟩ ⟨hsNew⟩ ⟨hliftCore⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryInternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryInternalProof
