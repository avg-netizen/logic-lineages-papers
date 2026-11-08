module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruencePayloadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalRepresentativeTag InternalApplicationCertificateConstructors
open InternalRepresentativeTagSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The right component of a pair-composition output is its second supplier's output. -/
theorem pairPayloadForward {n : Nat} (p q : Program n) (out payload : OTerm α)
    (xs : Fin n → OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph (pairOf p q) out xs)))
    (hp : Nonempty (Derivation body Gamma (programGraph q payload xs))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload out)) := by
  apply programCompositionCases InternalPairing.pairing ![p,q] out xs _ hw
  intro β j ys Delta hj hpair hg
  rw [graph1Rename]
  have hp' := renameInto hp j Delta hj
  rw [programRename] at hp'
  have hpair' : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (out.relabel j) (ys 0) (ys 1))) := by
    simpa only [graph2,twoTuple] using hpair
  have he := valueUnique q (ys 1) (payload.relabel j)
    (fun i => (xs i).relabel j) (hg 1) hp'
  exact outputTransport InternalUnpair.right (ys 1) (payload.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0) he
    (pairRight (out.relabel j) (ys 0) (ys 1) hpair')

/-- The reverse direction does not assume a witness for the raw right field:
the original composition graph supplies it and functionality identifies it. -/
theorem pairPayloadBackward {n : Nat} (p q : Program n) (out payload : OTerm α)
    (xs : Fin n → OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph (pairOf p q) out xs)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload out))) :
    Nonempty (Derivation body Gamma (programGraph q payload xs)) := by
  apply programCompositionCases InternalPairing.pairing ![p,q] out xs _ hw
  intro β j ys Delta hj hpair hg
  rw [programRename]
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  have hpair' : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (out.relabel j) (ys 0) (ys 1))) := by
    simpa only [graph2,twoTuple] using hpair
  have he := valueUnique InternalUnpair.right (ys 1) (payload.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0)
    (pairRight (out.relabel j) (ys 0) (ys 1) hpair') ht'
  exact outputTransport q (ys 1) (payload.relabel j)
    (fun i => (xs i).relabel j) he (hg 1)

theorem payloadForward (valid oldRepresentative : Program 1) (payload out raw : OTerm α)
    (hr : Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw)))
    (hp : Nonempty (Derivation body Gamma (graph1 (rightOf oldRepresentative) payload raw))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload out)) :=
  pairPayloadForward InternalUnpair.left (rightOf oldRepresentative) out payload
    (Fin.cons raw Fin.elim0) (representationPair valid oldRepresentative out raw hr) hp

theorem payloadBackward (valid oldRepresentative : Program 1) (payload out raw : OTerm α)
    (hr : Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload out))) :
    Nonempty (Derivation body Gamma (graph1 (rightOf oldRepresentative) payload raw)) :=
  pairPayloadBackward InternalUnpair.left (rightOf oldRepresentative) out payload
    (Fin.cons raw Fin.elim0) (representationPair valid oldRepresentative out raw hr) hp

/-- Exact-one validity selects the original wrapper's pair branch. -/
theorem representativeIntro (valid oldRepresentative : Program 1) (out raw : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 valid InternalOriginalStepGuard.one raw)))
    (hp : Nonempty (Derivation body Gamma
      (graph1 (pairOf InternalUnpair.left (rightOf oldRepresentative)) out raw))) :
    Nonempty (Derivation body Gamma (graph1 (representative valid oldRepresentative) out raw)) :=
  successorBranchIntro (GorbowVerifierNormalization.normalize valid)
    (InternalAcceptance.constantZero 1)
    (pairOf InternalUnpair.left (rightOf oldRepresentative)) out z
    (Fin.cons raw Fin.elim0)
    (normalizeAccept valid (Fin.cons raw Fin.elim0) hv) hp

/-- Reintroduce validity together with the exact original wrapper output. -/
theorem representationIntro (valid oldRepresentative : Program 1) (out raw : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph1 valid InternalOriginalStepGuard.one raw)))
    (hp : Nonempty (Derivation body Gamma
      (graph1 (pairOf InternalUnpair.left (rightOf oldRepresentative)) out raw))) :
    Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw)) := by
  obtain ⟨hr⟩ := representativeIntro valid oldRepresentative out raw hv hp
  obtain ⟨hv⟩ := hv
  exact ⟨Derivation.conjunctionIntroduction hv hr⟩

theorem actualOriginalRepresentativePayloadTransport :
    InternalRepresentativeApplicationCongruenceTargets.ActualOriginalRepresentativePayloadTransport := by
  intro body valid oldRepresentative α payload out raw
  apply InternalApplicationCertificateConstructorsProof.guardedIff
  · exact payloadBackward valid oldRepresentative payload out raw
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact payloadForward valid oldRepresentative payload out raw
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruencePayloadProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruencePayloadProof
