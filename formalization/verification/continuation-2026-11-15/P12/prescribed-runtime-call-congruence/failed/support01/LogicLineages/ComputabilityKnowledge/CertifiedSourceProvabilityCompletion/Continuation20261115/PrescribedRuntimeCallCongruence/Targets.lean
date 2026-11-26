module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open PrescribedRuntimeEquality
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Both exact original recipes and their literal term-prefix values. Native
input certificate numbers remain arbitrary, preserving original decode/default
behavior. No equality to an unspecified HasCertificates choice is asserted. -/
def InternalPrescribedTraces : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ ctx n tag (args others : List.Vector (Term 0) n) (codes : List.Vector Nat n),
 let J := tags I
 let a := args.map (rawNumeral (ctx := ctx))
 let b := others.map (rawNumeral (ctx := ctx))
 let h := codes.map (Term.numeral (n := ctx))
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj
   (.equal (tupleValue J a.toList) (rawNumeral (GorbowRegistryTuple.tupleTerm args.toList)))
   (.conj
    (.equal (callValue J (Term.numeral tag) a) (rawNumeral (GorbowPRDefiningEquations.call tag args)))
    (.conj
     (.equal (tupleCertificate J a b h) (Term.numeral (tupleNumber args others codes)))
     (.equal (callCertificate J (Term.numeral tag) a b h) (Term.numeral (callNumber tag args others codes)))))))
/-- Original tail-first tuple recursion and actual call/header certificate at
ONE unchanged installation, index, fuel, context0. Tag is an arbitrary numeric
term; its closed numeral-prefix validity/reflexivity is derived internally.
Only actual argument validator proofs and input equality certificates are supplied.
Zero-arity reflexive zero and both header reflexivities are not caller premises. -/
def InternalTupleAndCall : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ ctx (G : List (Formula ctx)) n (tag index fuel : Term ctx)
 (args others codes : List.Vector (Term ctx) n),
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (args.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (others.get i)))) →
 (∀ i : Fin n, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag (args.get i) (others.get i)) (codes.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj
   (accepted I.current.coreTag I.current.verifierTag index fuel
    (equalValue I.current.ctag I.current.atag (tupleValue (tags I) args.toList) (tupleValue (tags I) others.toList))
    (tupleCertificate (tags I) args others codes))
   (accepted I.current.coreTag I.current.verifierTag index fuel
    (equalValue I.current.ctag I.current.atag (callValue (tags I) tag args) (callValue (tags I) tag others))
    (callCertificate (tags I) tag args others codes))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Targets
