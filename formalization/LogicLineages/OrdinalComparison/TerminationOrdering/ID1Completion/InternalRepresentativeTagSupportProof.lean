module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalRepresentativeTag InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem twoTuple {X : Type} (ys : Fin 2 → X) :
    Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

/-- A pair-composition output and its first component graph determine the
output's left projection, using only the original internal graph rules. -/
theorem pairTagForward {n : Nat} (p q : Program n) (out tag : OTerm α)
    (xs : Fin n → OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph (pairOf p q) out xs)))
    (hp : Nonempty (Derivation body Gamma (programGraph p tag xs))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag out)) := by
  apply programCompositionCases InternalPairing.pairing ![p,q] out xs _ hw
  intro β j ys Delta hj hpair hg
  rw [graph1Rename]
  have hp' := renameInto hp j Delta hj
  rw [programRename] at hp'
  have hpair' : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (out.relabel j) (ys 0) (ys 1))) := by
    simpa only [graph2,twoTuple] using hpair
  have he := valueUnique p (ys 0) (tag.relabel j)
    (fun i => (xs i).relabel j) (hg 0) hp'
  exact outputTransport InternalUnpair.left (ys 0) (tag.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0) he
    (pairLeft (out.relabel j) (ys 0) (ys 1) hpair')

/-- The reverse direction does not assume a witness for the raw left field:
the original composition graph supplies it and functionality identifies it. -/
theorem pairTagBackward {n : Nat} (p q : Program n) (out tag : OTerm α)
    (xs : Fin n → OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph (pairOf p q) out xs)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag out))) :
    Nonempty (Derivation body Gamma (programGraph p tag xs)) := by
  apply programCompositionCases InternalPairing.pairing ![p,q] out xs _ hw
  intro β j ys Delta hj hpair hg
  rw [programRename]
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  have hpair' : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing (out.relabel j) (ys 0) (ys 1))) := by
    simpa only [graph2,twoTuple] using hpair
  have he := valueUnique InternalUnpair.left (ys 0) (tag.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0)
    (pairLeft (out.relabel j) (ys 0) (ys 1) hpair') ht'
  exact outputTransport p (ys 0) (tag.relabel j)
    (fun i => (xs i).relabel j) he (hg 0)

theorem representationPair (valid oldRepresentative : Program 1) (out raw : OTerm α)
    (hr : Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw))) :
    Nonempty (Derivation body Gamma
      (graph1 (pairOf InternalUnpair.left (rightOf oldRepresentative)) out raw)) := by
  obtain ⟨hr⟩ := hr
  exact successorBranchElim (GorbowVerifierNormalization.normalize valid)
    (InternalAcceptance.constantZero 1)
    (pairOf InternalUnpair.left (rightOf oldRepresentative)) out z
    (Fin.cons raw Fin.elim0)
    (normalizeAccept valid (Fin.cons raw Fin.elim0) ⟨Derivation.conjunctionLeft hr⟩)
    ⟨Derivation.conjunctionRight hr⟩

theorem tagForward (valid oldRepresentative : Program 1) (tag out raw : OTerm α)
    (hr : Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag raw))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag out)) :=
  pairTagForward InternalUnpair.left (rightOf oldRepresentative) out tag
    (Fin.cons raw Fin.elim0) (representationPair valid oldRepresentative out raw hr) ht

theorem tagBackward (valid oldRepresentative : Program 1) (tag out raw : OTerm α)
    (hr : Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag out))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag raw)) :=
  pairTagBackward InternalUnpair.left (rightOf oldRepresentative) out tag
    (Fin.cons raw Fin.elim0) (representationPair valid oldRepresentative out raw hr) ht

theorem tagsEqual (valid oldRepresentative : Program 1) (rawTag outTag out raw : OTerm α)
    (hr : Nonempty (Derivation body Gamma (representation valid oldRepresentative out raw)))
    (ht : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.left rawTag raw ⊓ graph1 InternalUnpair.left outTag out))) :
    Nonempty (Derivation body Gamma (equal rawTag outTag)) := by
  obtain ⟨ht⟩ := ht
  rw [equalEqn]
  exact valueUnique InternalUnpair.left rawTag outTag (Fin.cons out Fin.elim0)
    (tagForward valid oldRepresentative rawTag out raw hr ⟨Derivation.conjunctionLeft ht⟩)
    ⟨Derivation.conjunctionRight ht⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagSupportProof
