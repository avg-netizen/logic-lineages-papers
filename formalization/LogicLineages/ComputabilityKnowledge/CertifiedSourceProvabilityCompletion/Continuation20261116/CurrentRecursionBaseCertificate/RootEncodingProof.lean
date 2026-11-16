module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootEncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality FixedFormulaSubstitution
theorem root {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x)
 (tag : Nat) (raw : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.value I.previous.current.ctag I.previous.current.atag
   (rootFormula m tag) raw)
   (equalValue I.current.ctag I.current.atag
    (callValue (tags I) (Term.numeral tag)
     (LiteralNumeralPrefix.numeralCall (tags I).numeralTag (.zero : Term ctx) ::ᵥ raw))
    (callValue (tags I) (Term.numeral (tag+1)) raw)))) := by
 let J := tags I
 let e := PrescribedRuntimeSpecialization.runtimeEnvironment m
 obtain ⟨hc⟩ := CurrentCompositionCertificate.TermCopiesProof.equalFormula p
  I.previous.current.ctag I.previous.current.atag I.current.ctag I.current.atag
  I.previous.current.h_ctag I.previous.current.h_atag I.current.h_ctag I.current.h_atag e raw
  (GorbowPRDefiningEquations.call tag (.zero ::ᵥ argumentVariables m))
  (GorbowPRDefiningEquations.call (tag+1) (argumentVariables m))
 obtain ⟨hl⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J
  I.current.h_ctag I.current.h_atag I.previous.previous.previous.previous.hnumeral e raw tag
  (.zero ::ᵥ argumentVariables m)
 obtain ⟨hz⟩ := ValueTraceProof.numeral p J I.previous.previous.previous.previous.hnumeral (ctx := ctx) 0
 have hi : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (((.zero ::ᵥ argumentVariables m).map (termValue J.ctag J.atag e raw)).get i)
   ((LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx) ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨.mp (Logic.symmetryRule (GorbowPRNumeralCalculation.Theory p) _ _) hz⟩
  | succ i =>
   simp only [List.Vector.map_cons,List.Vector.get_cons_succ]
   rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues]
   exact ⟨.logical (.reflexive _)⟩
 obtain ⟨hargs⟩ := CurrentCompositionCertificate.ValueCongruenceProof.calls p J
  I.current.h_ctag I.current.h_atag (Term.numeral tag) _ _ hi
 have hleft := Logic.trans _ _ _ hl hargs
 obtain ⟨hr⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J
  I.current.h_ctag I.current.h_atag I.previous.previous.previous.previous.hnumeral e raw
  (tag+1) (argumentVariables m)
 rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues] at hr
 obtain ⟨he⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 0
  I.current.h_ctag I.current.h_atag I.current.h_ctag I.current.h_atag _ _ _ _ hleft hr
 exact ⟨Logic.trans _ _ _ hc he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootEncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootEncodingProof
