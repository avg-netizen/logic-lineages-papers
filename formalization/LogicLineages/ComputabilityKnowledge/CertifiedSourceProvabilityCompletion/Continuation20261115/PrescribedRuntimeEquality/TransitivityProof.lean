module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MatrixProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MPProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TransitivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem exactTransitivity : Targets.InternalTransitivity := by
 intro arity k p installedFormula lhs rhs arithmeticTerm old arithmetic x I ctx G t u v htu huv index fuel ht hu hv htuCore huvCore
 obtain ⟨ht⟩ := ht
 obtain ⟨hu⟩ := hu
 obtain ⟨hv⟩ := hv
 obtain ⟨htuCore⟩ := htuCore
 obtain ⟨huvCore⟩ := huvCore
 have hin : ∀ i : Fin 1, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag ((t ::ᵥ nil).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨ht⟩
  | succ i => exact Fin.elim0 i
 obtain ⟨hs⟩ := MatrixProof.certificate p _ _ _ I.current EnvironmentProof.transEnvironment
  EnvironmentProof.transMatrix G (t ::ᵥ nil) hin u v index fuel hu hv
 have hs' : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.current.coreTag index fuel
   (impValue I.current.ctag I.current.atag (equalValue I.current.ctag I.current.atag u v)
    (impValue I.current.ctag I.current.atag (equalValue I.current.ctag I.current.atag t u)
     (equalValue I.current.ctag I.current.atag t v)))
   (UniformClosedRule12Certificate.certificate I.current.ctag I.current.constructorTag
    (equalValue I.current.ctag I.current.atag t
     (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))) u v)) := by
  simpa only [EnvironmentProof.transValue,EnvironmentProof.transSpecialized] using hs
 exact MPProof.two p _ _ _ I.current I.previous.previous.previous.previous.mpTag
  I.previous.previous.previous.previous.hmp G
  (equalValue I.current.ctag I.current.atag u v) (equalValue I.current.ctag I.current.atag t u)
  (equalValue I.current.ctag I.current.atag t v) _ huv htu index fuel hs' huvCore htuCore
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TransitivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TransitivityProof
