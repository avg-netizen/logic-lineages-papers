module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Original tail-first tuple recursion and actual call/header certificate at
ONE unchanged installation, index, fuel, context0. Tag is an arbitrary numeric
term; its closed numeral-prefix validity/reflexivity is derived internally.
Only actual argument validator proofs and input equality certificates are supplied.
Zero-arity reflexive zero and both header reflexivities are not caller premises. -/
def InternalTupleAndCall : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ ctx (G : List (Formula ctx)) n (tag index fuel : Term ctx)
 (args others codes : List.Vector (Term ctx) n),
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (args.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (others.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag (args.get i) (others.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj
   (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
    (equalValue I.previous.current.ctag I.previous.current.atag (tupleValue (tags I.previous) args.toList) (tupleValue (tags I.previous) others.toList))
    (tupleCertificate (tags I.previous) args others codes))
   (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
    (equalValue I.previous.current.ctag I.previous.current.atag (callValue (tags I.previous) tag args) (callValue (tags I.previous) tag others))
    (callCertificate (tags I.previous) tag args others codes))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
