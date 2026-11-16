module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MatrixProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TermGuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.ReflexivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MPProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewMPProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityAlgebraTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
theorem exactUnaryCongruence : EqualityAlgebraTargets.InternalUnaryCongruence := by
 intro arity k p installedFormula lhs rhs arithmeticTerm old arithmetic x I n inputs e f ctx G raw t u htu index fuel hinputs ht hu htuCore
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue I.previous.current.ctag I.previous.current.atag e f raw t
 let fu := specializedValue I.previous.current.ctag I.previous.current.atag e f raw u
 obtain ⟨ht⟩ := ht
 obtain ⟨hu⟩ := hu
 obtain ⟨htuCore⟩ := htuCore
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
 obtain ⟨hrr⟩ := ReflexivityProof.current p installedFormula lhs rhs arithmeticTerm old arithmetic x I.previous G ft index fuel hft
 obtain ⟨hretain⟩ := CapabilitySupport.retentionInternal p installedFormula lhs rhs arithmeticTerm old arithmetic x I index fuel .zero _ _
 have hsNew := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hretain) hs'
 obtain ⟨hretainR⟩ := CapabilitySupport.retentionInternal p installedFormula lhs rhs arithmeticTerm old arithmetic x I index fuel .zero _ _
 have hrrNew := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hretainR) hrr
 exact NewMPProof.two p _ _ _ I.previous.current I.currentK I.previous.previous.previous.previous.previous.mpTag
  I.previous.previous.previous.previous.previous.hmp G
  (equalValue I.previous.current.ctag I.previous.current.atag t u) (equalValue I.previous.current.ctag I.previous.current.atag ft ft)
  (equalValue I.previous.current.ctag I.previous.current.atag ft fu) _ htu
  (RawCumulativeLogical.certificate I.previous.previous.previous.previous.previous.consTag
   I.previous.previous.previous.previous.previous.reflexivityTag ft) index fuel hsNew htuCore hrrNew
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
