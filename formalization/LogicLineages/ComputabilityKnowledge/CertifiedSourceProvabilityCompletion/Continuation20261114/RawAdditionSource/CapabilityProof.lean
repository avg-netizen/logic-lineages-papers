module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem singletonCapabilities {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) :
 SingletonCapabilities (GorbowPRNumeralCalculation.Theory p) p old a x I := by
 intro ctx t u v index fuel
 let E := I.toAddition.toCongruence.toEquality
 have hRef : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag t) (RawReflexivity.equalityValue I.ctag I.atag t))
    (RawCumulativeLogical.certificate I.ctag I.reflexivityTag t)))) := by
  obtain ⟨hc⟩ := RawEqualityComposition.StatementChecks.exactReflexivity n p old (arithmetic a) x E ctx t index fuel
  obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.utag I.qctag
   (RawRightReplaceCertificate.checker (RawCumulativeLogical.logical old) (arithmetic a) x) I.hu I.hqc
   index fuel .zero (.add (RawReflexivity.equalityValue I.ctag I.atag t) (RawReflexivity.equalityValue I.ctag I.atag t))
   (RawCumulativeLogical.certificate I.ctag I.reflexivityTag t)
  let H := RawReflexivityDispatcher.valid I.vtag t
  have ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hi) (.mp (.base hc) ht)))⟩
 have hReplacement : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (SixSol20261112.Fuel.success I.utag index fuel .zero
     (.add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u))
     (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u))))) := by
  obtain ⟨hc⟩ := RawRetainedSuccCongruence.ReplacementProof.replacementCore p old (arithmetic a) x I.toAddition.toCongruence t u index fuel
  obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.utag I.qctag
   (RawRightReplaceCertificate.checker (RawCumulativeLogical.logical old) (arithmetic a) x) I.hu I.hqc
   index fuel .zero (.add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u))
   (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u)
  let H := RawReflexivityDispatcher.valid I.vtag t
  let K := RawReflexivityDispatcher.valid I.vtag u
  have ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [K,H] H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hu : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [K,H] K := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (.mp (.base hi) (.mp (.mp (.base hc) ht) hu))))⟩
 have hzero := RawCumulativeArithmetic.StatementChecks.exactFuel n p (logical old) a x
  (RawAdditionComputation.Proof.baseInstallation p old a x I.toAddition) ctx t index fuel
 have hadd := RawAddSuccCertificate.StatementChecks.exactFuel n p (logical old) (RawAddZero.arithmeticLeaf a) x
  (RawAdditionComputation.Proof.stepInstallation p old a x I.toAddition) ctx t u index fuel
 have hright := RawRightReplaceCertificate.StatementChecks.exactFuel n p (RawCumulativeLogical.logical old) (arithmetic a) x
  E.toRight ctx t u v index fuel
 exact ⟨hRef,hzero,hadd,hReplacement,hright⟩

theorem computationCapabilities {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) :
 ComputationCapabilities (GorbowPRNumeralCalculation.Theory p) p old a x I := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · intro ctx t index fuel
   exact RawEqualityComposition.StatementChecks.exactReflexivity n p old (arithmetic a) x I.toAddition.toCongruence.toEquality ctx t index fuel
 · intro ctx t u cert index fuel
   exact RawEqualityComposition.StatementChecks.exactSymmetry n p old (arithmetic a) x I.toAddition.toCongruence.toEquality ctx t u cert index fuel
 · intro ctx t u v first second index fuel
   exact RawEqualityComposition.StatementChecks.exactTransitivity n p old (arithmetic a) x I.toAddition.toCongruence.toEquality ctx t u v first second index fuel
 · intro ctx t u cert index fuel
   exact RawRetainedSuccCongruence.StatementChecks.exactCoreCongruence n p old (arithmetic a) x I.toAddition.toCongruence ctx t u cert index fuel
 · intro ctx t index fuel
   exact RawAdditionComputation.StatementChecks.exactBase n p old a x I.toAddition ctx t index fuel
 · intro ctx t u v cert index fuel
   exact RawAdditionComputation.StatementChecks.exactStep n p old a x I.toAddition ctx t u v cert index fuel
 · intro ctx count t index fuel
   exact RawAdditionIteration.StatementChecks.exactIteration n p old a x I ctx count t index fuel

theorem liftSingleton {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) (T U : Sentence → Prop) (hsub : ∀ s, T s → U s)
 (h : SingletonCapabilities T p old a x I) : SingletonCapabilities U p old a x I := by
 intro ctx t u v index fuel
 obtain ⟨h1,h2,h3,h4,h5⟩ := h ctx t u v index fuel
 exact ⟨GorbowTheoryProofProof.monotonicity T U hsub ctx _ h1,
  GorbowTheoryProofProof.monotonicity T U hsub ctx _ h2,
  GorbowTheoryProofProof.monotonicity T U hsub ctx _ h3,
  GorbowTheoryProofProof.monotonicity T U hsub ctx _ h4,
  GorbowTheoryProofProof.monotonicity T U hsub ctx _ h5⟩

theorem liftComputation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) (T U : Sentence → Prop) (hsub : ∀ s, T s → U s)
 (h : ComputationCapabilities T p old a x I) : ComputationCapabilities U p old a x I := by
 obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := h
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · intro ctx t index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h1 ctx t index fuel)
 · intro ctx t u cert index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h2 ctx t u cert index fuel)
 · intro ctx t u v first second index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h3 ctx t u v first second index fuel)
 · intro ctx t u cert index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h4 ctx t u cert index fuel)
 · intro ctx t index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h5 ctx t index fuel)
 · intro ctx t u v cert index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h6 ctx t u v cert index fuel)
 · intro ctx count t index fuel
   exact GorbowTheoryProofProof.monotonicity T U hsub ctx _ (h7 ctx count t index fuel)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof.singletonCapabilities
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof.computationCapabilities
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof.liftSingleton
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.CapabilityProof.liftComputation
