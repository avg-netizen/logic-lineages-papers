module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem singleton {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (G : List (Formula ctx)) (isS : Bool) (A B C index fuel : Term ctx)
 (hg : Hilbert.Local T ctx G (UniformClosedPropositional.guards isS
  (RebaseProof.selected p f lhs rhs t old a x I isS).fval A B C)) :
 Nonempty (Hilbert.Local T ctx G
  (core I.currentK.coreTag index fuel
   (UniformClosedPropositional.conclusionValue isS I.previous.current.ctag I.previous.current.atag A B C)
   (UniformClosedPropositionalCertificate.certificate
    (RebaseProof.selected p f lhs rhs t old a x I isS).ctag
    (RebaseProof.selected p f lhs rhs t old a x I isS).constructorTag A B C))) := by
 let R := RebaseProof.rebase p f lhs rhs t old a x I isS
 obtain ⟨hc⟩ := UniformClosedPropositionalCertificate.CoreProof.internalCore p _ _ _ isS R A B C index fuel
 obtain ⟨hc⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hc⟩
 have hout := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hc) hg
 obtain ⟨he⟩ := RebaseProof.certificate p f lhs rhs t old a x I isS A B C
 obtain ⟨he⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨he⟩
 exact RebaseProof.coreCode T G I.currentK.coreTag index fuel _ _ _ (.base he) hout

theorem one {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (G : List (Formula ctx)) (A B seed ant index fuel : Term ctx)
 (hs : Hilbert.Local T ctx G
  (core I.currentK.coreTag index fuel (impValue I.previous.current.ctag I.previous.current.atag A B) seed))
 (ha : Hilbert.Local T ctx G (core I.currentK.coreTag index fuel A ant)) :
 Nonempty (Hilbert.Local T ctx G
  (core I.currentK.coreTag index fuel B
   (LiteralMPRun.certificate I.previous.previous.previous.previous.previous.mpTag .zero B seed ant))) := by
 let J := I.previous.current
 have hinput : Hilbert.Local T ctx G
  (LiteralCoreMP.inputAcceptance I.currentK.coreTag J.atag J.ctag .zero A B seed ant index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hs) ha
 have hd := SixSol20261112.Fuel.Equations.argumentChild p J.qtag HistoryLookup.reference
  (fun _ : Fin 1 => HistoryLookup.drop) J.h_qtag 0
 obtain ⟨hmp⟩ := LiteralCoreMP.StatementChecks.coreMP
  (CumulativePropositionalSource.logical f lhs rhs old) (CumulativePropositionalSource.arithmetic a) x arity p
  I.currentK.iteratorTag J.len J.atag J.ptag J.ctag J.rtag (HistoryLookup.LookupProof.dropTag J.qtag)
  J.qtag I.currentK.dispatcherTag I.currentK.h_iteratorTag J.h_len J.h_atag J.h_ptag J.h_ctag J.h_rtag hd J.h_qtag I.currentK.h_dispatcherTag
  I.previous.previous.previous.previous.previous.mpTag I.currentK.coreTag
  I.previous.previous.previous.previous.previous.hmp I.currentK.h_coreTag ctx .zero A B seed ant index fuel
 obtain ⟨hmp⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hmp⟩
 exact ⟨Hilbert.Local.mp (Hilbert.Local.base hmp) hinput⟩

theorem acceptedOfCore {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (G : List (Formula ctx)) (formula code index fuel : Term ctx)
 (hc : Hilbert.Local T ctx G (core I.currentK.coreTag index fuel formula code)) :
 Nonempty (Hilbert.Local T ctx G (accepted I.currentK.coreTag I.currentK.verifierTag index fuel formula code)) := by
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.currentK.verifierTag I.currentK.coreTag
  (UniformClosedPropositionalCertificate.checker _ _ _) I.currentK.h_verifierTag I.currentK.h_coreTag
  index fuel .zero (.add formula formula) code
 obtain ⟨hinj⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hinj⟩
 have hf := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hc
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hc) hf⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
