module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
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

open OriginalRawSyntaxTransportInternalConstructorSupportProof

theorem ordinary (n : Nat) (raw sourceHead base : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw sourceHead base)))
    (hhv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) sourceHead)))
    (hbv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) base)))
    : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hhj := renameInto hhv j Theta hj
  have hbj := renameInto hbv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hhj hbj
  let xs : Fin 1 → OTerm beta := ![raw.relabel j]
  have ht := ordinaryTag (.projection 0) (raw.relabel j) (sourceHead.relabel j) (base.relabel j) xs (projectionValue 0 xs) hcj
  have htag := unaryRecover InternalUnpair.left (.projection 0) (numeral 4) (raw.relabel j) xs ht (projectionValue 0 xs)
  have he := valueUnique InternalUnpair.left tag (numeral 4) xs (pairLeft _ _ _ hp) htag
  have hbase := ordinaryFirst (.projection 0) (raw.relabel j) (sourceHead.relabel j) (base.relabel j) xs (projectionValue 0 xs) hcj
  have heb := valueUnique (firstOf (.projection 0)) (base.relabel j) first xs hbase hf
  have hfv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (base.relabel j) first Fin.elim0 heb hbj
  have hpath := ordinaryHead (.projection 0) (raw.relabel j) (sourceHead.relabel j) (base.relabel j) xs (projectionValue 0 xs) hcj
  have hhead : Nonempty (Derivation body Theta
      (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) (sourceHead.relabel j) (raw.relabel j))) :=
    branchNumeralIntro 4 5 (leftOf (.projection 0)) _ _ (sourceHead.relabel j) xs ht hpath
  have heh := valueUnique (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) (sourceHead.relabel j) head xs hhead hh
  have hhv' := headTransport (OriginalHeadDecoderValidity.check n) (numeral 1) (sourceHead.relabel j) head Fin.elim0 heh hhj
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mpr
  exact ⟨orRight (orRight (orRight (orLeft (Derivation.conjunctionIntroduction
    (Classical.choice he) (Derivation.conjunctionIntroduction (Classical.choice hhv') (Classical.choice hfv))))))⟩

theorem numbered (n : Nat) (raw label sourceHead typ base types extra : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,sourceHead,typ,base,types,extra])))
    (hhv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) sourceHead)))
    (hbv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) base)))
    (hev : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) extra)))
    : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := renameInto hc j Theta hj
  rw [programRename] at hcj
  have hvec : (fun i : Fin 6 => (![label,sourceHead,typ,base,types,extra] i).relabel j) =
      ![label.relabel j,sourceHead.relabel j,typ.relabel j,base.relabel j,types.relabel j,extra.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec] at hcj
  have hhj := renameInto hhv j Theta hj
  have hbj := renameInto hbv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hhj hbj
  let xs : Fin 1 → OTerm beta := ![raw.relabel j]
  have ht := numberedTag (.projection 0) (raw.relabel j) (label.relabel j) (sourceHead.relabel j) (typ.relabel j) (base.relabel j) (types.relabel j) (extra.relabel j) xs (projectionValue 0 xs) hcj
  have htag := unaryRecover InternalUnpair.left (.projection 0) (numeral 5) (raw.relabel j) xs ht (projectionValue 0 xs)
  have he := valueUnique InternalUnpair.left tag (numeral 5) xs (pairLeft _ _ _ hp) htag
  have hbase := numberedFirst (.projection 0) (raw.relabel j) (label.relabel j) (sourceHead.relabel j) (typ.relabel j) (base.relabel j) (types.relabel j) (extra.relabel j) xs (projectionValue 0 xs) hcj
  have heb := valueUnique (firstOf (.projection 0)) (base.relabel j) first xs hbase hf
  have hfv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (base.relabel j) first Fin.elim0 heb hbj
  have hpath := pathValue (PairPath.right (PairPath.right (PairPath.left (PairPath.here (.projection 1)))))
    (.projection 0) (raw.relabel j) (sourceHead.relabel j)
    ![label.relabel j,sourceHead.relabel j,typ.relabel j,base.relabel j,types.relabel j,extra.relabel j]
    xs hcj (projectionValue 0 xs) (projectionValue 1 ![label.relabel j,sourceHead.relabel j,typ.relabel j,base.relabel j,types.relabel j,extra.relabel j])
  have hhead : Nonempty (Derivation body Theta
      (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) (sourceHead.relabel j) (raw.relabel j))) :=
    branchNumeralIntro 5 5 (leftOf (.projection 0)) _ _ (sourceHead.relabel j) xs ht hpath
  have heh := valueUnique (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) (sourceHead.relabel j) head xs hhead hh
  have hhv' := headTransport (OriginalHeadDecoderValidity.check n) (numeral 1) (sourceHead.relabel j) head Fin.elim0 heh hhj
  have hej := renameInto hev j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hej
  have hextra := numberedSecond (.projection 0) (raw.relabel j) (label.relabel j) (sourceHead.relabel j) (typ.relabel j) (base.relabel j) (types.relabel j) (extra.relabel j) xs (projectionValue 0 xs) hcj
  have hee := valueUnique (secondOf (.projection 0)) (extra.relabel j) second xs hextra hs
  have hsv := headTransport (OriginalCodeValidityGuard.check n) (numeral 1) (extra.relabel j) second Fin.elim0 hee hej
  apply (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mpr
  exact ⟨orRight (orRight (orRight (orRight (orLeft (Derivation.conjunctionIntroduction
    (Classical.choice he) (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction (Classical.choice hhv') (Classical.choice hfv)) (Classical.choice hsv)))))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
