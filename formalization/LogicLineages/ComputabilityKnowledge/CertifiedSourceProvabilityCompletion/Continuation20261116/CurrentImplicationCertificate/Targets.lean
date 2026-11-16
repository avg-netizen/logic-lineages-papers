module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
/-- Both exact original numeric recipes. Codes are arbitrary, not assumed
accepted or decodable; formulas are literal closed syntax. -/
def InternalTraces : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ ctx (A B C : Formula 0) (code hi ha : Nat),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.conj
   (.equal (liftCertificate I (formulaNumeral A) (formulaNumeral B) (Term.numeral code))
    (Term.numeral (n := ctx) (liftNumber A B code)))
   (.equal (mpUnderCertificate I (formulaNumeral A) (formulaNumeral B) (formulaNumeral C)
    (Term.numeral hi) (Term.numeral ha)) (Term.numeral (mpUnderNumber A B C hi ha)))))
/-- Actual new source/CORE/Fuel. Only original closed-formula guards and the
single input CORE certificate are premises; K is synthesized internally. -/
def InternalLift : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ ctx (G : List (Formula ctx)) (A B code index fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Hilbert.Local U ctx G (UniformClosedPropositional.formulaValid I.currentK.fval A)) →
 Nonempty (Hilbert.Local U ctx G (UniformClosedPropositional.formulaValid I.currentK.fval B)) →
 Nonempty (Hilbert.Local U ctx G (core I.currentK.coreTag index fuel A code)) →
 Nonempty (Hilbert.Local U ctx G (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (impValue J.ctag J.atag B A) (liftCertificate I A B code)))
/-- Same actual new source/CORE/Fuel. Original S order: first hi certifies
P→(Q→R), then ha certifies P→Q. No success/membership oracle. -/
def InternalMPUnder : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ ctx (G : List (Formula ctx)) (P Q R hi ha index fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Hilbert.Local U ctx G (UniformClosedPropositional.formulaValid I.currentS.fval P)) →
 Nonempty (Hilbert.Local U ctx G (UniformClosedPropositional.formulaValid I.currentS.fval Q)) →
 Nonempty (Hilbert.Local U ctx G (UniformClosedPropositional.formulaValid I.currentS.fval R)) →
 Nonempty (Hilbert.Local U ctx G
  (core I.currentK.coreTag index fuel (impValue J.ctag J.atag P (impValue J.ctag J.atag Q R)) hi)) →
 Nonempty (Hilbert.Local U ctx G (core I.currentK.coreTag index fuel (impValue J.ctag J.atag P Q) ha)) →
 Nonempty (Hilbert.Local U ctx G (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (impValue J.ctag J.atag P R) (mpUnderCertificate I P Q R hi ha)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.Targets
