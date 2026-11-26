module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambda (n : Nat) (raw typ child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw typ child)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  let xs : Fin 1 → OTerm beta := ![raw.relabel j]
  have ht := lambdaTag (.projection 0) (raw.relabel j) (typ.relabel j) (child.relabel j) xs (projectionValue 0 xs) hcj
  have htag := unaryRecover InternalUnpair.left (.projection 0) (numeral 1) (raw.relabel j) xs ht (projectionValue 0 xs)
  have he := valueUnique InternalUnpair.left tag (numeral 1) xs (pairLeft _ _ _ hp) htag
  have hchild := lambdaFirst (.projection 0) (raw.relabel j) (typ.relabel j) (child.relabel j) xs (projectionValue 0 xs) hcj
  have hec := valueUnique (firstOf (.projection 0)) (child.relabel j) first xs hchild hf
  have hfv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (child.relabel j) first Fin.elim0 hec hvj
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mpr
  exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction (Classical.choice he) (Classical.choice hfv)))⟩

theorem application (n : Nat) (raw typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw typ left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)))
    (hr : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hlj hrj
  let xs : Fin 1 → OTerm beta := ![raw.relabel j]
  have ht := applicationTag (.projection 0) (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) xs (projectionValue 0 xs) hcj
  have htag := unaryRecover InternalUnpair.left (.projection 0) (numeral 2) (raw.relabel j) xs ht (projectionValue 0 xs)
  have he := valueUnique InternalUnpair.left tag (numeral 2) xs (pairLeft _ _ _ hp) htag
  have hleft := applicationFirst (.projection 0) (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) xs (projectionValue 0 xs) hcj
  have hright := applicationSecond (.projection 0) (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) xs (projectionValue 0 xs) hcj
  have hel := valueUnique (firstOf (.projection 0)) (left.relabel j) first xs hleft hf
  have her := valueUnique (secondOf (.projection 0)) (right.relabel j) second xs hright hs
  have hfv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (left.relabel j) first Fin.elim0 hel hlj
  have hsv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (right.relabel j) second Fin.elim0 her hrj
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mpr
  exact ⟨orRight (orRight (orLeft (Derivation.conjunctionIntroduction
    (orLeft (Classical.choice he))
    (Derivation.conjunctionIntroduction (Classical.choice hfv) (Classical.choice hsv)))))⟩

theorem cons (n : Nat) (raw typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)))
    (hr : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hlj hrj
  let xs : Fin 1 → OTerm beta := ![raw.relabel j]
  have ht := consTag (.projection 0) (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) xs (projectionValue 0 xs) hcj
  have htag := unaryRecover InternalUnpair.left (.projection 0) (numeral 7) (raw.relabel j) xs ht (projectionValue 0 xs)
  have he := valueUnique InternalUnpair.left tag (numeral 7) xs (pairLeft _ _ _ hp) htag
  have hleft := consFirst (.projection 0) (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) xs (projectionValue 0 xs) hcj
  have hright := consSecond (.projection 0) (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) xs (projectionValue 0 xs) hcj
  have hel := valueUnique (firstOf (.projection 0)) (left.relabel j) first xs hleft hf
  have her := valueUnique (secondOf (.projection 0)) (right.relabel j) second xs hright hs
  have hfv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (left.relabel j) first Fin.elim0 hel hlj
  have hsv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (right.relabel j) second Fin.elim0 her hrj
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mpr
  exact ⟨orRight (orRight (orLeft (Derivation.conjunctionIntroduction
    (orRight (Classical.choice he))
    (Derivation.conjunctionIntroduction (Classical.choice hfv) (Classical.choice hsv)))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
