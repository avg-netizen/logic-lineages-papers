module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.GraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.TaggedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm trans)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem branchTag (i : Fin 6) (tag payload : OTerm alpha)
    (h : Nonempty (Derivation body Delta (CasesProof.branch i tag payload))) :
    Nonempty (Derivation body Delta (eqn tag (numeral i.val))) := by
  unfold CasesProof.branch at h
  split_ifs at h with hi
  · exact andLeft h
  · exact h

theorem branchBasic (i : Fin 6) (tag payload : OTerm alpha) (hi : i.val < 2)
    (h : Nonempty (Derivation body Delta (CasesProof.branch i tag payload))) :
    Nonempty (Derivation body Delta (eqn payload (numeral 0))) := by
  simp only [CasesProof.branch,if_pos hi] at h
  exact andRight h

theorem tagged (i j : Fin 6) (f g p q ef eg : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f (numeral i.val) p)))
    (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing g (numeral j.val) q)))
    (hp : i.val < 2 → Nonempty (Derivation body Delta (eqn p (numeral 0))))
    (hq : j.val < 2 → Nonempty (Derivation body Delta (eqn q (numeral 0))))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)))
    (he : Nonempty (Derivation body Delta (eqn ef eg))) :
    Nonempty (Derivation body Delta (eqn f g)) := by
  obtain ⟨hfc⟩ := GraphProof.outputCode i f p ef hf hef
  obtain ⟨hgc⟩ := GraphProof.outputCode j g q eg hg heg
  obtain ⟨he⟩ := he
  have hc : Derivation body Delta (eqn (ArithmeticProof.code i p) (ArithmeticProof.code j q)) :=
    trans (symm hfc) (trans he hgc)
  by_cases hij : i = j
  · subst j
    have hpq : Nonempty (Derivation body Delta (eqn p q)) := by
      by_cases hi : i.val < 2
      · obtain ⟨hp⟩ := hp hi
        obtain ⟨hq⟩ := hq hi
        exact ⟨trans hp (symm hq)⟩
      · exact ArithmeticProof.payloadCancel i p q (Nat.le_of_not_gt hi) hc
    have hft := InternalApplicationValidityStackAppendRunProof.rightTransport
      InternalPairing.pairing f (numeral i.val) p q hpq hf
    exact valueUnique InternalPairing.pairing f g ![numeral i.val,q] hft hg
  · obtain ⟨hfalse⟩ := ArithmeticProof.different i j p q hij hc
    exact ⟨Derivation.explosion hfalse⟩

theorem atBranches (i j : Fin 6) (f g ft fp gt gp ef eg : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f ft fp)))
    (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing g gt gp)))
    (hb1 : Nonempty (Derivation body Delta (CasesProof.branch i ft fp)))
    (hb2 : Nonempty (Derivation body Delta (CasesProof.branch j gt gp)))
    (hef : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)))
    (heg : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)))
    (he : Nonempty (Derivation body Delta (eqn ef eg))) :
    Nonempty (Derivation body Delta (eqn f g)) := by
  have hf' := headTransport InternalPairing.pairing f ft (numeral i.val) (Fin.cons fp Fin.elim0)
    (branchTag i ft fp hb1) hf
  have hg' := headTransport InternalPairing.pairing g gt (numeral j.val) (Fin.cons gp Fin.elim0)
    (branchTag j gt gp hb2) hg
  exact tagged i j f g fp gp ef eg hf' hg' (fun hi => branchBasic i ft fp hi hb1)
    (fun hj => branchBasic j gt gp hj hb2) hef heg he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.TaggedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.TaggedProof
