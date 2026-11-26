module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Both ORIGINAL numeric traces, with arbitrary input certificate numbers
(including malformed decode/default behavior), computed by the same installed
runtime terms. This does not equate an unspecified existential producer choice. -/
def InternalPrescribedTraces : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ ctx (t u v : Term 0) (f : Term 1) (htu huv : Nat),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj
   (.equal (transitivityCertificate I.previous.previous.previous.previous.mpTag I.current.ctag I.current.atag I.current.constructorTag
    (rawNumeral t) (rawNumeral u) (rawNumeral v) (Term.numeral htu) (Term.numeral huv))
    (Term.numeral (n := ctx) (transitivityNumber t u v htu huv)))
   (.equal (unaryCertificate I.previous.previous.previous.previous.mpTag I.current.ctag I.current.atag I.current.constructorTag
    I.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.reflexivityTag boundEnvironment f nil
    (rawNumeral t) (rawNumeral u) (Term.numeral htu))
    (Term.numeral (unaryNumber f t u htu)))))
/-- No intermediate acceptance or logical instance success premise. Two caller
certificates are the actual input facts, with the original reversed MP order. -/
def InternalTransitivity : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ ctx (G : List (Formula ctx)) (t u v htu huv index fuel : Term ctx),
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag t)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag u)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag v)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag t u) htu)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag u v) huv)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel
   (equalValue I.current.ctag I.current.atag t v)
   (transitivityCertificate I.previous.previous.previous.previous.mpTag I.current.ctag I.current.atag I.current.constructorTag t u v htu huv)))
/-- Runtime-environment generality is essential for composition/recursion.
Reflexivity of f[t] is constructed internally from this same installation,
not supplied as a success premise; original closed runtime coordinates remain guarded. -/
def InternalUnaryCongruence : Prop :=
 ∀ arity k (p : Program arity) (installedFormula : Formula 1) (lhs rhs : Term 1) (arithmeticTerm : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p installedFormula lhs rhs arithmeticTerm old arithmetic x),
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (t u htu index fuel : Term ctx),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag t)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.current.vtag u)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.current.coreTag index fuel (equalValue I.current.ctag I.current.atag t u) htu)) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel
   (equalValue I.current.ctag I.current.atag
    (specializedValue I.current.ctag I.current.atag e f raw t)
    (specializedValue I.current.ctag I.current.atag e f raw u))
   (unaryCertificate I.previous.previous.previous.previous.mpTag I.current.ctag I.current.atag I.current.constructorTag
    I.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.reflexivityTag e f raw t u htu)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Targets
