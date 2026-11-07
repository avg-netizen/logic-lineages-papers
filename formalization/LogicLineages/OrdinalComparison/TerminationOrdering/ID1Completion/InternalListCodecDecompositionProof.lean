module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalListCodec InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalTagArithmeticSyntaxProof InternalControlGraphSupportProof InternalOriginalOrderSyntaxProof

theorem actualOriginalNonzeroListReconstruction :
    InternalListCodecDecompositionTargets.ActualOriginalNonzeroListReconstruction := by
  intro body α n h t
  let A := (eqn n z).not ⊓ ((unaryGraph headCode h n) ⊓ (unaryGraph tailCode t n))
  have hn : Nonempty (Derivation body [A] (eqn n z).not) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hh : Nonempty (Derivation body [A] (unaryGraph headCode h n)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  have ht : Nonempty (Derivation body [A] (unaryGraph tailCode t n)) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  obtain ⟨d⟩ := reconstructNonzero n h t hn hh ht
  simpa only [equalEqn] using
    (show Nonempty (Derivation body [] (A.imp (consGraph n h t))) from
      ⟨Derivation.implicationIntroduction d⟩)

theorem actualOriginalNonzeroTailDescent :
    InternalListCodecDecompositionTargets.ActualOriginalNonzeroTailDescent := by
  intro body α n t
  let A := (eqn n z).not ⊓ (unaryGraph tailCode t n)
  have hn : Nonempty (Derivation body [A] (eqn n z).not) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have ht : Nonempty (Derivation body [A] (unaryGraph tailCode t n)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨d⟩ := nonzeroTailDescent n t hn ht
  simpa only [equalEqn,InternalLessThan.strictLess] using
    (show Nonempty (Derivation body [] (A.imp (ltF t n))) from
      ⟨Derivation.implicationIntroduction d⟩)

theorem actualOriginalConsTailDescent :
    InternalListCodecDecompositionTargets.ActualOriginalConsTailDescent := by
  intro body α n h t
  obtain ⟨d⟩ := consTailDescent (body := body) (Gamma := [consGraph n h t]) n h t
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
