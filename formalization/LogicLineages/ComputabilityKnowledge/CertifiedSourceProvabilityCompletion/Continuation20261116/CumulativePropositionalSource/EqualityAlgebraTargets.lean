module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityAlgebraTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
/-- No intermediate acceptance or logical instance success premise. Two caller
certificates are the actual input facts, with the original reversed MP order. -/
def InternalTransitivity : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ ctx (G : List (Formula ctx)) (t u v htu huv index fuel : Term ctx),
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag t)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag u)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag v)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag t u) htu)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag u v) huv)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag t v)
   (transitivityCertificate I.previous.previous.previous.previous.previous.mpTag I.previous.current.ctag I.previous.current.atag I.previous.current.constructorTag t u v htu huv)))
/-- Runtime-environment generality is essential for composition/recursion.
Reflexivity of f[t] is constructed internally from this same installation,
not supplied as a success premise; original closed runtime coordinates remain guarded. -/
def InternalUnaryCongruence : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (t u htu index fuel : Term ctx),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag t)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag u)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag t u) htu)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue I.previous.current.ctag I.previous.current.atag
    (specializedValue I.previous.current.ctag I.previous.current.atag e f raw t)
    (specializedValue I.previous.current.ctag I.previous.current.atag e f raw u))
   (unaryCertificate I.previous.previous.previous.previous.previous.mpTag I.previous.current.ctag I.previous.current.atag I.previous.current.constructorTag
    I.previous.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.previous.reflexivityTag e f raw t u htu)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityAlgebraTargets
