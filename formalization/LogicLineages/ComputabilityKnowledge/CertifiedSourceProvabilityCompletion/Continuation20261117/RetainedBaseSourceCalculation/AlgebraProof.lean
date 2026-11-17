module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.SymbolicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.AlgebraProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence


open SixSol20261112.Fuel NamedArithmeticGraph

theorem rawValid {arity k ctx : Nat} (p : Program arity) (f : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (G : List (Formula ctx)) (tag : Nat) (value : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (rawCall (tags I.previous) tag value))) := by
 apply CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old a x I.previous G
 intro i
 have hi : i = 0 := Fin.eq_zero i
 subst i
 exact CorrectedAugmentationErasure.AlgebraProof.rawValid p f lhs rhs t old a x I G value

theorem join {arity k ctx : Nat} (p : Program arity) (f : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (U : Sentence → Prop) (incl : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → U sigma)
 (r s z h1 h2 index fuel : Term ctx)
 (hr : ∀ G, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag r)))
 (hs : ∀ G, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag s)))
 (hz : ∀ G, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag z)))
 (hleft : Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (equalValue (tags I.previous).ctag (tags I.previous).atag r s) h1)))
 (hright : Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (equalValue (tags I.previous).ctag (tags I.previous).atag s z) h2))) :
 Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (equalValue (tags I.previous).ctag (tags I.previous).atag r z)
  (transitivityCertificate (tags I.previous).mtag (tags I.previous).ctag (tags I.previous).atag
   (tags I.previous).constructorTag r s z h1 h2))) := by
 let A := core I.currentK.coreTag index fuel (equalValue (tags I.previous).ctag (tags I.previous).atag r s) h1
 let B := core I.currentK.coreTag index fuel (equalValue (tags I.previous).ctag (tags I.previous).atag s z) h2
 let G := [A,B]
 have h := CumulativePropositionalSource.NewTransitivityProof.exactTransitivity arity k p f lhs rhs t old a x I
  ctx G r s z h1 h2 index fuel (hr G) (hs G) (hz G)
  ⟨.hypothesis (by change A ∈ [A,B]; exact List.mem_cons_self)⟩
  ⟨.hypothesis (by change B ∈ [A,B]; exact List.mem_cons_of_mem A List.mem_cons_self)⟩
 obtain ⟨hL⟩ := CurrentStructuralProducerCore.CoreTools.project U _ _ index fuel _ h1 hleft
 obtain ⟨hR⟩ := CurrentStructuralProducerCore.CoreTools.project U _ _ index fuel _ h2 hright
 have hh : ∀ phi, phi ∈ G → Nonempty (Hilbert.Local U ctx [] phi) := by
  intro phi hm
  simp only [G,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with he | he
  · subst phi; exact ⟨.base hL⟩
  · subst phi; exact ⟨.base hR⟩
 obtain ⟨hout⟩ := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl hh h
 exact ⟨hout.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.AlgebraProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.AlgebraProof
