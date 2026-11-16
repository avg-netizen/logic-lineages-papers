module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leafPair (n : Nat) (raw payload : OTerm alpha) (tag : Fin 2)
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing raw (numeral (if tag.val=0 then 0 else 3)) payload))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta t p first second head hj hpair hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hpj
  have ht := valueUnique InternalUnpair.left t (numeral (if tag.val=0 then 0 else 3)) ![raw.relabel j]
    (pairLeft _ _ _ hpair) (pairLeft _ _ _ hpj)
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) t p first second head hpair hf hs hh).mpr
  fin_cases tag
  · exact ⟨orLeft (orLeft (Classical.choice ht))⟩
  · exact ⟨orLeft (orRight (Classical.choice ht))⟩

theorem variableValid (n : Nat) (raw index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) :=
  leafPair n raw index 0 (variableConstructorPair raw index hc)

theorem bottom (n : Nat) (raw typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) :=
  leafPair n raw typ 1 (bottomConstructorPair raw typ hc)

theorem nil (n : Nat) (raw : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  have hp := binaryRecover InternalPairing.pairing (constant 0 6) (constant 0 0)
    raw (numeral 6) z Fin.elim0 hc (constantValue 6 Fin.elim0) (constantValue 0 Fin.elim0)
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta t p first second head hj hpair hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.zRelabel] at hpj
  have ht := valueUnique InternalUnpair.left t (numeral 6) ![raw.relabel j]
    (pairLeft _ _ _ hpair) (pairLeft _ _ _ hpj)
  have hz := valueUnique InternalUnpair.right p z ![raw.relabel j]
    (pairRight _ _ _ hpair) (pairRight _ _ _ hpj)
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) t p first second head hpair hf hs hh).mpr
  exact ⟨orRight (orRight (orRight (orRight (orRight
    (Derivation.conjunctionIntroduction (Classical.choice ht) (Classical.choice hz))))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
