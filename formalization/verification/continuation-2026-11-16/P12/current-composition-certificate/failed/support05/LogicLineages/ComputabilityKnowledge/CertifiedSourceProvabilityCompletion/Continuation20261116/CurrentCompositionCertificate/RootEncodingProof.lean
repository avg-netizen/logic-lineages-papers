module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValueCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootEncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality FixedFormulaSubstitution
 theorem variables {m ctx : Nat} (J : Tags) (raw : List.Vector (Term ctx) m) :
 (argumentVariables m).map (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment m) raw) = raw := by
 apply List.Vector.ext
 intro i
 simp [argumentVariables,termValue,PrescribedRuntimeSpecialization.runtimeEnvironment]
theorem root {arity k m n ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x)
 (f : Program n) (g : Fin n → Program m) tag (raw : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.value I.previous.current.ctag I.previous.current.atag
   (rootFormula f g tag) raw)
   (equalValue I.current.ctag I.current.atag (callValue (tags I) (Term.numeral tag) raw)
    (callValue (tags I) (Term.numeral (tag+1)) (childValues (tags I) f g tag raw))))) := by
 let J := tags I
 let e := PrescribedRuntimeSpecialization.runtimeEnvironment m
 let children := List.Vector.ofFn (fun i => GorbowPRDefiningEquations.call (tag+GorbowPRChildTags.argumentTag f g i) (argumentVariables m))
 obtain ⟨hc⟩ := TermCopiesProof.equalFormula p I.previous.current.ctag I.previous.current.atag
  I.current.ctag I.current.atag I.previous.current.h_ctag I.previous.current.h_atag
  I.current.h_ctag I.current.h_atag e raw
  (GorbowPRDefiningEquations.call tag (argumentVariables m)) (GorbowPRDefiningEquations.call (tag+1) children)
 obtain ⟨hl⟩ := CallEncodingProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral e raw tag (argumentVariables m)
 rw [variables] at hl
 obtain ⟨hr⟩ := CallEncodingProof.call p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral e raw (tag+1) children
 have hi : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((children.map (termValue J.ctag J.atag e raw)).get i) ((childValues J f g tag raw).get i))) := by
  intro i
  obtain ⟨h⟩ := CallEncodingProof.call p J I.current.h_ctag I.current.h_atag
   I.previous.previous.previous.previous.hnumeral e raw (tag+GorbowPRChildTags.argumentTag f g i) (argumentVariables m)
  rw [variables] at h
  simpa only [children,childValues,List.Vector.get_map,List.Vector.get_ofFn] using (show Nonempty _ from ⟨h⟩)
 obtain ⟨hh⟩ := ValueCongruenceProof.calls p J I.current.h_ctag I.current.h_atag
  (Term.numeral (tag+1)) _ _ hi
 have hright := Logic.trans _ _ _ hr hh
 obtain ⟨he⟩ := CodecProof.binary p J.ctag J.atag J.ctag J.atag 0
  I.current.h_ctag I.current.h_atag I.current.h_ctag I.current.h_atag _ _ _ _ hl hright
 exact ⟨Logic.trans _ _ _ hc he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootEncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootEncodingProof
