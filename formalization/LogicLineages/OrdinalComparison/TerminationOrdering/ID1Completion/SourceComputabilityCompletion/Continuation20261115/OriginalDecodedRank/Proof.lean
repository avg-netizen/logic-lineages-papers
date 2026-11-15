module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalContextInsertionSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atPairs (n : Nat) (node param left right out child a b parentRank childRank : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child a b)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) out node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hr : Nonempty (Derivation body Delta (graph2 (rank n) parentRank node param)))
    (hc : Nonempty (Derivation body Delta (graph2 (rank n) childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) := by
  apply formulaCases (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param)
  · have ha : Nonempty (Derivation body
        (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param :: Delta)
        (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := SupportProof.rankEquality n node param left right parentRank (withHyp hp _) ha (withHyp hr _)
    have hs := OriginalDecodedDependencyClosure.Proof.dependenciesClosed n body alpha (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param :: Delta) node param out child a b
      (withHyp hv _) (withHyp hm _) (withHyp hq _)
    have hca := SupportProof.childAccepted n child param a b (withHyp hq _) (andLeft hs) (andRight hs)
    have hce := SupportProof.rankEquality n child param a b childRank (withHyp hq _) hca (withHyp hc _)
    have hd := OriginalDecodedDependencies.Proof.dependencyDescent n body alpha (graph2 (OriginalDecodedDependencies.accepted n) (suc z) node param :: Delta) node param left right out child a b
      (withHyp hp _) (withHyp hv _) (withHyp hm _) (withHyp hq _)
    exact InternalOriginalPairingOrderArithmeticProof.strictTransport childRank parentRank a left hce he (andLeft hd)
  · exact OriginalDecodedDependencies.Proof.rejectedImpossible n node param out child _
      (withHyp hv _) (withHyp hm _) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem atParent (n : Nat) (node param left right out child parentRank childRank : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) out node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hr : Nonempty (Derivation body Delta (graph2 (rank n) parentRank node param)))
    (hc : Nonempty (Derivation body Delta (graph2 (rank n) childRank child param)))
    : Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) := by
  apply SupportProof.pairCases child _
  intro beta j Theta a b hj hq
  rw [strictRename]
  have hp' := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hp'
  have hv' := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hv'
  have hm' := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hr'
  have hc' := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc'
  exact atPairs n (node.relabel j) (param.relabel j) (left.relabel j) (right.relabel j)
    (out.relabel j) (child.relabel j) a b (parentRank.relabel j) (childRank.relabel j) hp' hq hv' hm' hr' hc'

theorem rankDecrease : Targets.InternalRankDecrease := by
  intro n body alpha Delta node param out child parentRank childRank hv hm hr hc
  apply SupportProof.pairCases node _
  intro beta j Theta left right hj hp
  rw [strictRename]
  have hv' := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hv'
  have hm' := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hr'
  have hc' := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hc'
  exact atParent n (node.relabel j) (param.relabel j) left right (out.relabel j) (child.relabel j)
    (parentRank.relabel j) (childRank.relabel j) hp hv' hm' hr' hc'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Proof
