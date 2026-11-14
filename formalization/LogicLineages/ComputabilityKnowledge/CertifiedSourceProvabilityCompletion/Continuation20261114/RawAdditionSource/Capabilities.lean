module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Original five singleton families at the identical installed newest verifier. -/
def SingletonCapabilities {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t u v index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag t) (RawReflexivity.equalityValue I.ctag I.atag t))
    (RawCumulativeLogical.certificate I.ctag I.reflexivityTag t)))) ∧
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawAddZero.equalityValue I.ctag I.atag t) (RawAddZero.equalityValue I.ctag I.atag t))
    (RawCumulativeArithmetic.certificate I.ctag I.zeroTag t)))) ∧
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (SixSol20261112.Fuel.success I.utag index fuel .zero
     (.add (RawAddSucc.equalityValue I.ctag I.atag t u) (RawAddSucc.equalityValue I.ctag I.atag t u))
     (RawAddSuccCertificate.certificate I.ctag I.addTag t u))))) ∧
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (SixSol20261112.Fuel.success I.utag index fuel .zero
     (.add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u))
     (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u))))) ∧
 Nonempty (Derivation T
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawReflexivityDispatcher.valid I.vtag v)
     (SixSol20261112.Fuel.success I.utag index fuel .zero
      (.add (RawRightReplace.formulaValue I.ctag I.atag t u v) (RawRightReplace.formulaValue I.ctag I.atag t u v))
      (RawRightReplaceCertificate.certificate I.ctag I.qtag t u v))))))

def ReflexivityCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel t t (RawEqualityComposition.reflexivityCertificate I.ctag I.reflexivityTag t))))

def SymmetryCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t u cert index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel t u cert)
     (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel u t
      (RawEqualityComposition.symmetryCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag t u cert))))))

def TransitivityCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t u v first second index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawReflexivityDispatcher.valid I.vtag v)
     (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel t u first)
      (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel u v second)
       (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel t v
        (RawEqualityComposition.transitivityCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag t u v first second))))))))

def CongruenceCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t u cert index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawSuccCongruence.inputRaw I.ctag I.atag t u) (RawSuccCongruence.inputRaw I.ctag I.atag t u)) cert) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
       (.add (RawSuccCongruence.outputRaw I.ctag I.atag t u) (RawSuccCongruence.outputRaw I.ctag I.atag t u))
       (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag t u cert)) (.succ .zero))))))

def AdditionBaseCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
    (RawAdditionComputation.addRaw I.ctag I.atag t (RawAdditionComputation.zeroRaw I.ctag)) t (RawCumulativeArithmetic.certificate I.ctag I.zeroTag t))))

def AdditionStepCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (t u v cert index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawReflexivityDispatcher.valid I.vtag v)
     (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel (RawAdditionComputation.addRaw I.ctag I.atag t u) v cert)
      (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
       (RawAdditionComputation.addRaw I.ctag I.atag t (RawAdditionComputation.succRaw I.ctag u)) (RawAdditionComputation.succRaw I.ctag v)
       (RawAdditionComputation.stepCertificate I.mpTag I.qtag I.replaceTag I.reflexivityTag I.addTag I.ctag I.atag t u v cert)))))))

def AdditionIterationCapability {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ∀ ctx (count t index fuel : Term ctx),
 Nonempty (Derivation (T)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.conj (.equal (RawIteratedSucc.first I.leftTag (RawAdditionIteration.binaryCall I.iteratorTag count t))
     (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag count))
    (.conj (.equal (RawIteratedSucc.second I.leftTag I.rightTag (RawAdditionIteration.binaryCall I.iteratorTag count t))
      (RawAdditionIteration.binaryCall I.prefixTag count t))
     (.conj (RawReflexivityDispatcher.valid I.vtag (RawAdditionIteration.binaryCall I.prefixTag count t))
      (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
       (RawAdditionComputation.addRaw I.ctag I.atag t (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag count))
       (RawAdditionIteration.binaryCall I.prefixTag count t)
       (RawIteratedSucc.third I.rightTag (RawAdditionIteration.binaryCall I.iteratorTag count t))))))))

def ComputationCapabilities {n : Nat} (T : Sentence → Prop) (p : Program n) (old a : Program 1) (x : Program 3)
 (I : RawAdditionIteration.Installation p old a x) : Prop :=
 ReflexivityCapability T p old a x I ∧
 SymmetryCapability T p old a x I ∧
 TransitivityCapability T p old a x I ∧
 CongruenceCapability T p old a x I ∧
 AdditionBaseCapability T p old a x I ∧
 AdditionStepCapability T p old a x I ∧
 AdditionIterationCapability T p old a x I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource
