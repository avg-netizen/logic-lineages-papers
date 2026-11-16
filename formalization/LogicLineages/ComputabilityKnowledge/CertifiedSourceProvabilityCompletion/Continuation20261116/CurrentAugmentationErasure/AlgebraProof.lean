module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.AlgebraProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
theorem rawValid {arity k ctx : Nat} (root : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation root installed lhs rhs t old a x)
 (G : List (Formula ctx)) (input : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory root) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag
   (LiteralNumeralPrefix.numeralCall (tags I.previous).numeralTag input))) :=
 PrescribedRuntimeCallCongruence.ValidityProof.numeral root _ _ _ I.previous.current
  (tags I.previous).numeralTag I.previous.previous.previous.previous.previous.hnumeral G input

theorem childValid {arity k n ctx : Nat} (root : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation root installed lhs rhs t old a x)
 (G : List (Formula ctx)) (p : Program 1) (q : Program n) (tag : Nat) (input : Term ctx) (i : Fin 2) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory root) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((children (tags I.previous) p q tag input).get i))) := by
 simp only [children, CurrentCompositionCertificate.childValues, List.Vector.get_ofFn]
 apply CurrentCompositionCertificate.ValidityProof.call root installed lhs rhs t old a x I.previous G
 intro j
 have hj : j = 0 := Fin.eq_zero j
 subst j
 exact rawValid root installed lhs rhs t old a x I G input

theorem assemble {arity k n ctx : Nat} (root : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation root installed lhs rhs t old a x)
 (G : List (Formula ctx)) (p : Program 1) (q : Program n) (tag : Nat) (input index fuel : Term ctx)
 (hroot : Hilbert.Local (GorbowPRNumeralCalculation.Theory root) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag (left (tags I.previous) tag input) (middle (tags I.previous) p q tag input))
   (PrescribedSourceAxiomSpecialization.certificate (tags I.previous).mtag (tags I.previous).ctag (tags I.previous).atag (tags I.previous).constructorTag
    (CurrentCompositionCertificate.rootFormula (.projection (0 : Fin 2)) (branches p q) tag)
    (LiteralNumeralPrefix.numeralCall (tags I.previous).numeralTag input ::ᵥ nil))))
 (hproj : Hilbert.Local (GorbowPRNumeralCalculation.Theory root) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag (middle (tags I.previous) p q tag input) (right (tags I.previous) p q tag input))
   (PrescribedSourceAxiomSpecialization.certificate (tags I.previous).mtag (tags I.previous).ctag (tags I.previous).atag (tags I.previous).constructorTag
    (projectionFormula tag) (children (tags I.previous) p q tag input)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory root) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag (left (tags I.previous) tag input) (right (tags I.previous) p q tag input))
   (certificate (tags I.previous) p q tag input))) := by
 have hl := CurrentCompositionCertificate.ValidityProof.call root installed lhs rhs t old a x I.previous G
  (Term.numeral tag) (LiteralNumeralPrefix.numeralCall (tags I.previous).numeralTag input ::ᵥ nil) (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact rawValid root installed lhs rhs t old a x I G input)
 have hm := CurrentCompositionCertificate.ValidityProof.call root installed lhs rhs t old a x I.previous G
  (Term.numeral (tag+1)) (children (tags I.previous) p q tag input)
  (childValid root installed lhs rhs t old a x I G p q tag input)
 have hr := childValid root installed lhs rhs t old a x I G p q tag input 0
 exact CumulativePropositionalSource.NewTransitivityProof.exactTransitivity arity k root installed lhs rhs t old a x I
  ctx G _ _ _ _ _ index fuel hl hm hr ⟨hroot⟩ ⟨hproj⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.AlgebraProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.AlgebraProof
