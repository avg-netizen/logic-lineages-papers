module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.AlgebraProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
theorem exactErasure : Targets.InternalErasure := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let root := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let T := GorbowPRNumeralCalculation.Theory root
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let K := tags R.previous
 have incl := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨bound,hseed⟩ := CumulativePropositionalSource.SeedProof.seeded installed lhs rhs t old a baseX pF pR c hA hn R
 refine ⟨bound,?_⟩
 intro n p q tag hnode ctx input fuel
 let G := [orderGuard (Term.numeral bound) fuel]
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let av := LiteralNumeralPrefix.numeralCall K.numeralTag input ::ᵥ nil
 let bv := children K p q tag input
 have hg : Nonempty (Hilbert.Local U ctx G (orderGuard (Term.numeral bound) fuel)) := ⟨.hypothesis List.mem_cons_self⟩
 have hav : ∀ i, Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid R.previous.previous.current.vtag (av.get i))) := by
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  have h := AlgebraProof.rawValid root installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R G input
  exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl (fun psi hm => ⟨.hypothesis hm⟩) h
 have hb : ∀ i, Nonempty (Hilbert.Local U ctx G (RawReflexivityDispatcher.valid R.previous.previous.current.vtag (bv.get i))) := by
  intro i
  have h := AlgebraProof.childValid root installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R G p q tag input i
  exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl (fun psi hm => ⟨.hypothesis hm⟩) h
 let rf := CurrentCompositionCertificate.rootFormula (.projection (0 : Fin 2)) (branches p q) tag
 obtain ⟨hs⟩ := hseed 1 rf (CurrentCompositionCertificate.RootProof.member root _ _ tag hnode) ctx G av fuel hav hg
 obtain ⟨hp⟩ := hseed 2 (projectionFormula tag) (SyntaxProof.projectionMember root p q tag hnode) ctx G bv fuel hb hg
 have hsc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 have hpc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hp
 obtain ⟨he⟩ := CurrentCompositionCertificate.RootEncodingProof.root root installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)
  R.previous (.projection (0 : Fin 2)) (branches p q) tag av
 obtain ⟨heS⟩ := GorbowTheoryProofProof.monotonicity T U incl ctx _ ⟨he⟩
 obtain ⟨hroot⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U G R.currentK.coreTag index fuel _ _ _ (.base heS) hsc
 obtain ⟨heP⟩ := EncodingProof.projection root installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R tag bv
 obtain ⟨hePS⟩ := GorbowTheoryProofProof.monotonicity T U incl ctx _ ⟨heP⟩
 obtain ⟨hproj⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U G R.currentK.coreTag index fuel _ _ _ (.base hePS) hpc
 let PA := core R.currentK.coreTag index fuel (equalValue K.ctag K.atag (left K tag input) (middle K p q tag input))
  (PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag R.previous.previous.current.constructorTag rf av)
 let PB := core R.currentK.coreTag index fuel (equalValue K.ctag K.atag (middle K p q tag input) (right K p q tag input))
  (PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag R.previous.previous.current.constructorTag (projectionFormula tag) bv)
 let Gamma := [PA,PB]
 have ha := AlgebraProof.assemble root installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R Gamma p q tag input index fuel
  (.hypothesis (by change PA ∈ [PA,PB]; exact List.mem_cons_self))
  (.hypothesis (by change PB ∈ [PA,PB]; exact List.mem_cons_of_mem PA List.mem_cons_self))
 have hh : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hm
  simp only [Gamma,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with he | he
  · subst psi; exact ⟨hroot⟩
  · subst psi; exact ⟨hproj⟩
 obtain ⟨hout⟩ := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl hh ha
 exact ⟨hout.discharge.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.SourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.SourceProof
