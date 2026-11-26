module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate

/-- Both original recipes; input code numbers remain arbitrary, including
malformed decode/default behavior. No unspecified HasCertificates choice. -/
def InternalTraces : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ ctx (P : Formula 0) (f : Term 1) (left middle right : Term 0) (htu huv : Nat),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.conj
   (.equal (unaryRuleCertificate I boundEnvironment f nil
    (rawNumeral left) (rawNumeral middle)) (Term.numeral (n := ctx) (unaryRuleNumber f left middle)))
   (.equal (transitivityUnderCertificate I (formulaNumeral P) (rawNumeral left) (rawNumeral middle)
    (rawNumeral right) (Term.numeral htu) (Term.numeral huv))
    (Term.numeral (transitivityUnderNumber P left middle right htu huv)))))
/-- Runtime environment supports the accumulator coordinate with other closed
runtime inputs. No acceptance input: the original ordinary implication is
synthesized solely from original term validator premises. -/
def InternalUnaryRule : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (left right index fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 (∀ i, Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag left)) →
 Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag right)) →
 Nonempty (Hilbert.Local U ctx G (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (impValue J.ctag J.atag (equalValue J.ctag J.atag left right)
   (equalValue J.ctag J.atag (specializedValue J.ctag J.atag e f raw left)
    (specializedValue J.ctag J.atag e f raw right)))
  (unaryRuleCertificate I e f raw left right)))
/-- Original ordinary conditional transitivity. Premises are the two checked
IMPLICATION certificates at the actual new CORE; neither a bare left/middle
nor middle/right equality certificate is assumed. Original MP order retained. -/
def InternalTransitivityUnder : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1),
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ ctx (G : List (Formula ctx)) (P left middle right htu huv index fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Hilbert.Local U ctx G (UniformClosedPropositional.formulaValid I.currentK.fval P)) →
 Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag left)) →
 Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag middle)) →
 Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag right)) →
 Nonempty (Hilbert.Local U ctx G (core I.currentK.coreTag index fuel
  (impValue J.ctag J.atag P (equalValue J.ctag J.atag left middle)) htu)) →
 Nonempty (Hilbert.Local U ctx G (core I.currentK.coreTag index fuel
  (impValue J.ctag J.atag P (equalValue J.ctag J.atag middle right)) huv)) →
 Nonempty (Hilbert.Local U ctx G (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (impValue J.ctag J.atag P (equalValue J.ctag J.atag left right))
  (transitivityUnderCertificate I P left middle right htu huv)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.Targets
