module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalContextInsertionSyntaxProof
open InductionDefinitions InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawStep (n : Nat) (raw : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (AtRaw n raw)) := by
  apply BindingProof.atRawIntro n raw
  let r : OTerm (alpha ⊕ Fin 6) := raw.relabel Sum.inl
  let fuel1 : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let bound1 : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let table1 : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let fuel2 : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let bound2 : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let table2 : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields n r fuel1 bound1 table1 fuel2 bound2 table2
  let Theta := A :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
  have hf : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi (Sum.inl : alpha → alpha ⊕ Fin 6) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at hij
  obtain ⟨h⟩ := CoreProof.rawStep n r fuel1 bound1 table1 fuel2 bound2 table2 hij hf
  exact ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (n : Nat) (raw : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw n raw)) :=
  BindingProof.rawInduction n raw (fun _ _ r hi => rawStep n r hi)

theorem transport (n : Nat) (raw fuel1 bound1 table1 fuel2 bound2 table2 : OTerm alpha)
    (hb1 : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc bound1))))
    (hb2 : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc bound2))))
    (hf1 : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw fuel1)))
    (hf2 : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw fuel2)))
    (ht1 : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) table1 fuel1 bound1)))
    (ht2 : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) table2 fuel2 bound2)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) raw table1))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) raw table2)) :=
  BindingProof.atRawApply n raw fuel1 bound1 table1 fuel2 bound2 table2 (allRaw n raw)
    (andIntro (andIntro (andIntro hb1 hb2) (andIntro hf1 hf2)) (andIntro (andIntro ht1 ht2) hl))

theorem sufficientFuelCoherence : Targets.InternalSufficientFuelCoherence := by
  intro n body alpha Delta raw fuel1 bound1 table1 fuel2 bound2 table2 hb1 hb2 hf1 hf2 ht1 ht2
  exact ⟨transport n raw fuel1 bound1 table1 fuel2 bound2 table2 hb1 hb2 hf1 hf2 ht1 ht2,
    transport n raw fuel2 bound2 table2 fuel1 bound1 table1 hb2 hb1 hf2 hf1 ht2 ht1⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Proof
