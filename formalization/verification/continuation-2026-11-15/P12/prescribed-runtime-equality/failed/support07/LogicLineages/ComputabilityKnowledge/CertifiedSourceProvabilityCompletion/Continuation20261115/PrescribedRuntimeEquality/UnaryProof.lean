module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MatrixProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TermGuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.ReflexivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MPProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.UnaryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem exactUnaryCongruence : Targets.InternalUnaryCongruence := by
 intro arity k p installedFormula lhs rhs arithmeticTerm old arithmetic x I n inputs e f ctx G raw t u htu index fuel hinputs ht hu htuCore
 let T := GorbowPRNumeralCalculation.Theory p
 let ft := specializedValue I.current.ctag I.current.atag e f raw t
 let fu := specializedValue I.current.ctag I.current.atag e f raw u
 obtain ⟨ht⟩ := ht
 obtain ⟨hu⟩ := hu
 obtain ⟨htuCore⟩ := htuCore
 obtain ⟨hft⟩ := TermGuardProof.specialized p _ _ _ I.current e f G raw t hinputs ht
 have hin : ∀ i : Fin (inputs+1), Nonempty (Hilbert.Local T ctx G
  (RawReflexivityDispatcher.valid I.current.vtag ((ft ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hft⟩
  | succ j => exact hinputs j
 obtain ⟨hs⟩ := MatrixProof.certificate p _ _ _ I.current (EnvironmentProof.prepend e)
  (EnvironmentProof.matrix f) G (ft ::ᵥ raw) hin t u index fuel ht hu
 have hs' : Hilbert.Local T ctx G
  (core I.current.coreTag index fuel
   (impValue I.current.ctag I.current.atag (equalValue I.current.ctag I.current.atag t u)
    (impValue I.current.ctag I.current.atag (equalValue I.current.ctag I.current.atag ft ft)
     (equalValue I.current.ctag I.current.atag ft fu)))
   (UniformClosedRule12Certificate.certificate I.current.ctag I.current.constructorTag
    (equalValue I.current.ctag I.current.atag ft (FixedFormulaSubstitution.termValue I.current.ctag I.current.atag e raw f)) t u)) := by
  simpa only [EnvironmentProof.matrixValue,EnvironmentProof.matrixSpecialized,ft,fu] using hs
 obtain ⟨hrr⟩ := ReflexivityProof.current p installedFormula lhs rhs arithmeticTerm old arithmetic x I G ft index fuel hft
 exact MPProof.two p _ _ _ I.current I.previous.previous.previous.previous.mpTag
  I.previous.previous.previous.previous.hmp G
  (equalValue I.current.ctag I.current.atag t u) (equalValue I.current.ctag I.current.atag ft ft)
  (equalValue I.current.ctag I.current.atag ft fu) _ htu
  (RawCumulativeLogical.certificate I.previous.previous.previous.previous.consTag
   I.previous.previous.previous.previous.reflexivityTag ft) index fuel hs' htuCore hrr
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.UnaryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.UnaryProof
