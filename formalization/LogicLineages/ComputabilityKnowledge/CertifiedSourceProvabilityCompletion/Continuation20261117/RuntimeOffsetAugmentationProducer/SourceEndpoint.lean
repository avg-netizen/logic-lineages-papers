module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourcePreflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem exactSource : SourceTargets.InstalledSource := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let root := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let K := tags I.previous
 have incl := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨bound,herase⟩ := CorrectedAugmentationErasure.SourceProof.exactErasure installed lhs rhs k t old a baseX pF pR c hA hn I
 refine ⟨bound,?_⟩
 intro n p q tag producerTag hnode hproducer ctx value fuel
 let offset := argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let G := [orderGuard (Term.numeral bound) fuel]
 obtain ⟨he⟩ := herase n p q tag hnode ctx value fuel
 have ha : Hilbert.Local U ctx G _ := .mp (.base he) (.hypothesis List.mem_cons_self)
 have hc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ha
 have HI : CurrentCallCongruenceProgram.Installation root K :=
  ⟨I.previous.current.h_ctag,I.previous.current.h_atag,I.previous.previous.previous.previous.previous.hnumeral,
   I.previous.previous.previous.previous.previous.hmp,I.previous.current.h_constructor,
   I.previous.previous.previous.previous.previous.hc,I.previous.previous.previous.previous.previous.hreflexivity⟩
 obtain ⟨hg⟩ := GraphProof.exactGraph _ root K HI I.currentK.ptag I.previous.previous.current.constructorTag
  I.currentK.h_ptag I.previous.previous.current.h_constructor n p q tag offset producerTag rfl hproducer ctx value
 obtain ⟨hgS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨hg⟩
 obtain ⟨hc'⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U G I.currentK.coreTag index fuel _ _ _
  (.base (Support.equalitySymmetry _ _ hgS)) hc
 obtain ⟨hout⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore root installed lhs rhs t old a
  (SaturatedAxiomLeaf.saturated baseX) I U incl G _ _ index fuel hc'
 exact ⟨hout.discharge.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourceEndpoint
