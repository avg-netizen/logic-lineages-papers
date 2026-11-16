module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

/-- Select actual installed K/S, preserving every genuine node membership. -/
def selected {arity k : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x) (isS : Bool) :
 UniformClosedPropositionalCertificate.Installation p
  (CumulativePropositionalSource.previousLogical f lhs rhs old) (CumulativePropositionalSource.arithmetic a) x isS :=
 match isS with | false => I.currentK | true => I.currentS
/-- Reuse previously installed cons/append programs and the common currentK
checker program. This changes numeric tags only with their actual memberships,
not by assuming equal tags or changing the source/root. -/
def rebase {arity k : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x) (isS : Bool) :
 UniformClosedPropositionalCertificate.Installation p
  (CumulativePropositionalSource.previousLogical f lhs rhs old) (CumulativePropositionalSource.arithmetic a) x isS :=
 { selected p f lhs rhs t old a x I isS with
   ctag := I.previous.current.ctag
   atag := I.previous.current.atag
   h_ctag := I.previous.current.h_ctag
   h_atag := I.previous.current.h_atag
   coreTag := I.currentK.coreTag
   h_coreTag := I.currentK.h_coreTag
   verifierTag := I.currentK.verifierTag
   h_verifierTag := I.currentK.h_verifierTag }
/-- Internal coherence of the two actual cons occurrences, for arbitrary raw
constructor output. No native-image premise or certificate validity is used. -/
theorem certificate {arity k : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x) (isS : Bool) {ctx : Nat} (A B C : Term ctx) :
 let K := selected p f lhs rhs t old a x I isS
 let R := rebase p f lhs rhs t old a x I isS
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedPropositionalCertificate.certificate R.ctag R.constructorTag A B C)
   (UniformClosedPropositionalCertificate.certificate K.ctag K.constructorTag A B C))) := by
 exact GorbowPRInternalCoherence.Proof.registryCoherence arity p I.previous.current.ctag
  (selected p f lhs rhs t old a x I isS).ctag 2 HistoryCodec.cons
  I.previous.current.h_ctag (selected p f lhs rhs t old a x I isS).h_ctag ctx
  (UniformClosedPropositional.lineCall (selected p f lhs rhs t old a x I isS).constructorTag A B C ::ᵥ .zero ::ᵥ nil)
/-- Equality of certificate numbers transports a fixed CORE call. -/
theorem coreCode {ctx : Nat} (T : Sentence → Prop) (G : List (Formula ctx))
 (tag : Nat) (index fuel formula a b : Term ctx)
 (hab : Hilbert.Local T ctx G (.equal a b))
 (ha : Hilbert.Local T ctx G (core tag index fuel formula a)) :
 Nonempty (Hilbert.Local T ctx G (core tag index fuel formula b)) := by
 have he : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add formula formula) a)
   (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add formula formula) b)) := by
  apply LiteralRawMP.DispatcherSupportProof.callCongruence (T := T) (G := G) tag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive index))
  | succ i => cases i using Fin.cases with
    | zero => exact .base (.logical (.reflexive fuel))
    | succ i => cases i using Fin.cases with
      | zero => exact .base (.logical (.reflexive (.zero : Term ctx)))
      | succ i => cases i using Fin.cases with
        | zero => exact .base (.logical (.reflexive (.add formula formula)))
        | succ i => cases i using Fin.cases with
          | zero => exact hab
          | succ i => exact Fin.elim0 i
 exact ⟨localTrans _ _ _ (Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) he) ha⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
