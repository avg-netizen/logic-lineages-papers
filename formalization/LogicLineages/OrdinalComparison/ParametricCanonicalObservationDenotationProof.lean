module
public import LogicLineages.OrdinalComparison.ParametricCanonicalObservationTargets
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteDenotationProof
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentProof
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseRepresentationProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseRecursionProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation.Proof

open ParametricSourceSuccessor

theorem omegaFreeTransport : Targets.OmegaFreeTransport := by
  intro G c hc ι ν t hν ht
  induction t with
  | var x => rfl
  | zero => rfl
  | one => rfl
  | omega => exact False.elim ht
  | add a b iha ihb =>
      simp only [denoteUsing, denoteWith, iha ht.1, ihb ht.2]
  | emul a b iha ihb =>
      simp only [denoteUsing, denoteWith, iha ht.1, ihb ht.2]
  | collapse a b iha ihb =>
      obtain ⟨m, hm⟩ := SourceRestrictedAssignmentFinite.Proof.finiteDenotation
        ι G ν a hν ht.1
      obtain ⟨n, hn⟩ := SourceRestrictedAssignmentFinite.Proof.finiteDenotation
        ι G ν b hν ht.2
      simp only [denoteUsing, denoteWith, iha ht.1, ihb ht.2]
      rw [hm, hn]
      change (c (ParametricFiniteCollapseArgument.argument m n) : Ordinal) =
        (ParametricActualCollapse.collapseWith G (ParametricFiniteCollapseArgument.argument m n) : Ordinal)
      apply congrArg (fun k : Nat => (k : Ordinal))
      apply ParametricActualCollapse.Proof.uniqueBelowEpsilonZero G c hc
      rw [ParametricFiniteCollapseArgument.Proof.exactArgument]
      exact (ParametricFinitePairCollapse.Proof.pair_facts (m, n)).1

end LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation.Proof
