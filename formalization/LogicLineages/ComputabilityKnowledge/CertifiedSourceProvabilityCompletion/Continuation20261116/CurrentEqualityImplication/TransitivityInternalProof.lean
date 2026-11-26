module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.RulesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityInternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem internal {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (tTemplate : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs tTemplate old a x)
 (G : List (Formula ctx)) (P t u v htu huv index fuel : Term ctx)
 (hP : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval P)))
 (ht : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag t)))
 (hu : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag u)))
 (hv : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag v)))
 (htuCore : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (impValue I.previous.current.ctag I.previous.current.atag P
   (equalValue I.previous.current.ctag I.previous.current.atag t u)) htu)))
 (huvCore : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (impValue I.previous.current.ctag I.previous.current.atag P
   (equalValue I.previous.current.ctag I.previous.current.atag u v)) huv))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (impValue I.previous.current.ctag I.previous.current.atag P (equalValue I.previous.current.ctag I.previous.current.atag t v))
   (transitivityUnderCertificate I P t u v htu huv))) := by
 obtain ⟨ht⟩ := ht
 obtain ⟨hu⟩ := hu
 obtain ⟨hv⟩ := hv
 obtain ⟨htuCore⟩ := htuCore
 obtain ⟨huvCore⟩ := huvCore
 have hin : ∀ i : Fin 1, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((t ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨ht⟩
  | succ i => exact Fin.elim0 i
 obtain ⟨hs⟩ := MatrixProof.certificate p _ _ _ I.previous.current EnvironmentProof.transEnvironment
  EnvironmentProof.transMatrix G (t ::ᵥ nil) hin u v index fuel hu hv
 have hs' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.previous.current.coreTag index fuel
   (impValue I.previous.current.ctag I.previous.current.atag (equalValue I.previous.current.ctag I.previous.current.atag u v)
    (impValue I.previous.current.ctag I.previous.current.atag (equalValue I.previous.current.ctag I.previous.current.atag t u)
     (equalValue I.previous.current.ctag I.previous.current.atag t v)))
   (UniformClosedRule12Certificate.certificate I.previous.current.ctag I.previous.current.constructorTag
    (equalValue I.previous.current.ctag I.previous.current.atag t
     (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))) u v)) := by
  simpa only [EnvironmentProof.transValue,EnvironmentProof.transSpecialized] using hs
 obtain ⟨hretain⟩ := CumulativePropositionalSource.CapabilitySupport.retentionInternal p installed lhs rhs tTemplate old a x I index fuel .zero _ _
 have hsNew := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hretain) hs'
 obtain ⟨hP⟩ := hP
 let J := I.previous.current
 let TU := equalValue J.ctag J.atag t u
 let UV := equalValue J.ctag J.atag u v
 let TV := equalValue J.ctag J.atag t v
 obtain ⟨hTUK⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G false t u ht hu
 obtain ⟨hUVK⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G false u v hu hv
 obtain ⟨hTVK⟩ := GuardProof.equal p installed lhs rhs tTemplate old a x I G false t v ht hv
 obtain ⟨hinnerK⟩ := GuardProof.implication p installed lhs rhs tTemplate old a x I G false TU TV hTUK hTVK
 obtain ⟨hseedK⟩ := GuardProof.implication p installed lhs rhs tTemplate old a x I G false UV _ hUVK hinnerK
 obtain ⟨hlift⟩ := RulesProof.lift p installed lhs rhs tTemplate old a x I G
  (impValue J.ctag J.atag UV (impValue J.ctag J.atag TU TV)) P _ index fuel ⟨hseedK⟩ ⟨hP⟩ ⟨hsNew⟩
 have hliftCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hlift
 obtain ⟨hPS⟩ := GuardProof.copy p installed lhs rhs tTemplate old a x I G true P hP
 obtain ⟨hTUS⟩ := GuardProof.copy p installed lhs rhs tTemplate old a x I G true TU hTUK
 obtain ⟨hUVS⟩ := GuardProof.copy p installed lhs rhs tTemplate old a x I G true UV hUVK
 obtain ⟨hTVS⟩ := GuardProof.copy p installed lhs rhs tTemplate old a x I G true TV hTVK
 obtain ⟨hinnerS⟩ := GuardProof.copy p installed lhs rhs tTemplate old a x I G true _ hinnerK
 obtain ⟨hfirst⟩ := RulesProof.mPUnder p installed lhs rhs tTemplate old a x I G P UV
  (impValue J.ctag J.atag TU TV) _ huv index fuel ⟨hPS⟩ ⟨hUVS⟩ ⟨hinnerS⟩ ⟨hliftCore⟩ ⟨huvCore⟩
 have hfirstCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hfirst
 exact RulesProof.mPUnder p installed lhs rhs tTemplate old a x I G P TU TV _ htu index fuel
  ⟨hPS⟩ ⟨hTUS⟩ ⟨hTVS⟩ ⟨hfirstCore⟩ ⟨htuCore⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityInternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.TransitivityInternalProof
