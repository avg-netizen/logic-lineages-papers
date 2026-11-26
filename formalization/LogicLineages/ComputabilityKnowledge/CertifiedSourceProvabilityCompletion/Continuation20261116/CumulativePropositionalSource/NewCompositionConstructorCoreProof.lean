module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorCoreProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open CurrentCompositionCertificate
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
theorem assemble {arity k m n ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : JointInstallation p installed lhs rhs t old a x)
 (f : Program n) (g : Fin n → Program m) tag (G : List (Formula ctx))
 (inputs : List.Vector (Term ctx) m) (values codes : List.Vector (Term ctx) n)
 (result functionCode index fuel : Term ctx) :
 let J := tags I.previous
 let av := numeralValues J.numeralTag inputs
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag values
 let parent := callValue J (Term.numeral tag) av
 let left := callValue J (Term.numeral (tag+1)) bv
 let right := callValue J (Term.numeral (tag+1)) cv
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.previous.current.ctag
  I.previous.previous.current.atag I.previous.previous.current.constructorTag (rootFormula f g tag) av
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag parent left) seed)) →
 (∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag right
   (LiteralNumeralPrefix.numeralCall J.numeralTag result)) functionCode)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue J.ctag J.atag parent (LiteralNumeralPrefix.numeralCall J.numeralTag result))
   (certificate I.previous f g tag inputs values result codes functionCode))) := by
 dsimp only
 intro hroot hchildren hfunction
 let J := tags I.previous
 let av := numeralValues J.numeralTag inputs
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag values
 have hav : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (av.get i))) := by
  intro i
  simpa only [av,numeralValues,List.Vector.get_map] using
   (PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
    I.previous.previous.previous.previous.previous.hnumeral G (inputs.get i))
 have hcv : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (cv.get i))) := by
  intro i
  simpa only [cv,numeralValues,List.Vector.get_map] using
   (PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
    I.previous.previous.previous.previous.previous.hnumeral G (values.get i))
 have hbv : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (bv.get i))) := by
  intro i
  simpa only [bv,childValues,List.Vector.get_ofFn] using
   (CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
    (Term.numeral (tag+GorbowPRChildTags.argumentTag f g i)) av hav)
 obtain ⟨hparent⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G (Term.numeral tag) av hav
 obtain ⟨hleft⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G (Term.numeral (tag+1)) bv hbv
 obtain ⟨hright⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G (Term.numeral (tag+1)) cv hcv
 obtain ⟨hout⟩ := PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
  I.previous.previous.previous.previous.previous.hnumeral G result
 obtain ⟨hboth⟩ := NewCallRuntimeProof.exactTupleAndCall
  arity k p installed lhs rhs t old a x I ctx G n (Term.numeral (tag+1)) index fuel bv cv codes hbv hcv hchildren
 have hcall := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hboth
 have hcallCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcall
 obtain ⟨hfirst⟩ := NewTransitivityProof.exactTransitivity
  arity k p installed lhs rhs t old a x I ctx G _ _ _ _ _ index fuel
  ⟨hparent⟩ ⟨hleft⟩ ⟨hright⟩ hroot ⟨hcallCore⟩
 have hfirstCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hfirst
 exact NewTransitivityProof.exactTransitivity
  arity k p installed lhs rhs t old a x I ctx G _ _ _ _ _ index fuel
  ⟨hparent⟩ ⟨hright⟩ ⟨hout⟩ ⟨hfirstCore⟩ hfunction
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorCoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorCoreProof
