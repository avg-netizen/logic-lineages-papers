module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralRecursionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry Family Construction

/-- The source AST induction supplies EVERY node, including recursion. -/
theorem allNodeCertificates : ∀ m (q : Program m), NodeCertificates q := by
  intro m q
  induction q with
  | zero => exact BasicNodes.zero
  | succ => exact BasicNodes.successor
  | projection i => exact BasicNodes.projection i
  | composition f g hf hg => exact Construction.composition f g hf hg
  | recursion f g hf hg => exact Construction.recursion f g hf hg

theorem tagParametricCertificates : TagTargets.TagParametricCertificates := by
  intro m q
  obtain ⟨produce,hPR,hgood⟩ := allNodeCertificates m q
  refine ⟨produce,hPR,?_⟩
  intro n p tag ht inputs
  exact Transport.numericMonotonicity (NodeSupport.check q tag) (registryAxiomCheck p)
    (fun raw h => NodeSupport.checkIntoRegistry q p tag ht raw h) 0 _ _ (hgood (tag,inputs))

theorem fixedProgramCertificates : Targets.FixedProgramCertificates := by
  intro n p tag m q ht
  obtain ⟨produce,hPR,hgood⟩ := tagParametricCertificates m q
  refine ⟨fun inputs => produce (tag,inputs), hPR.comp ((Primrec.const tag).pair Primrec.id), ?_⟩
  intro inputs
  exact hgood n p tag ht inputs

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Proof
