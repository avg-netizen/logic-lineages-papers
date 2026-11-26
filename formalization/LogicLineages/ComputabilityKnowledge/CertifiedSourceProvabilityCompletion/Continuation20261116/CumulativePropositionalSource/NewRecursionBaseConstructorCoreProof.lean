module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.RootEncodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewRecursionBaseConstructorCoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseCertificate
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality FixedFormulaSubstitution
theorem assemble {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : JointInstallation p installed lhs rhs t old a x)
 (tag : Nat) (G : List (Formula ctx)) (inputs : List.Vector (Term ctx) m)
 (result childCode index fuel : Term ctx) :
 let J := tags I.previous
 let av := numeralValues J.numeralTag inputs
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 let parent := callValue J (Term.numeral tag) (zero ::ᵥ av)
 let child := callValue J (Term.numeral (tag+1)) av
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.previous.current.ctag
  I.previous.previous.current.atag I.previous.previous.current.constructorTag (rootFormula m tag) av
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag parent child) seed)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag child
   (LiteralNumeralPrefix.numeralCall J.numeralTag result)) childCode)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue J.ctag J.atag parent (LiteralNumeralPrefix.numeralCall J.numeralTag result))
   (certificate I.previous tag inputs result childCode))) := by
 dsimp only
 intro hroot hchild
 let J := tags I.previous
 let av := numeralValues J.numeralTag inputs
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 have hav : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag (av.get i))) := by
  intro i
  simpa only [av,numeralValues,CurrentCompositionCertificate.numeralValues,List.Vector.get_map] using
   (PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
    I.previous.previous.previous.previous.previous.hnumeral G (inputs.get i))
 have hz := PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
  I.previous.previous.previous.previous.previous.hnumeral G (.zero : Term ctx)
 have hargs : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag ((zero ::ᵥ av).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact hz
  | succ i => exact hav i
 obtain ⟨hparent⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
  (Term.numeral tag) (zero ::ᵥ av) hargs
 obtain ⟨hchildValid⟩ := CurrentCompositionCertificate.ValidityProof.call p installed lhs rhs t old a x I.previous G
  (Term.numeral (tag+1)) av hav
 obtain ⟨hout⟩ := PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current J.numeralTag
  I.previous.previous.previous.previous.previous.hnumeral G result
 exact NewTransitivityProof.exactTransitivity
  arity k p installed lhs rhs t old a x I ctx G _ _ _ _ _ index fuel
  ⟨hparent⟩ ⟨hchildValid⟩ ⟨hout⟩ hroot hchild
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewRecursionBaseConstructorCoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewRecursionBaseConstructorCoreProof
