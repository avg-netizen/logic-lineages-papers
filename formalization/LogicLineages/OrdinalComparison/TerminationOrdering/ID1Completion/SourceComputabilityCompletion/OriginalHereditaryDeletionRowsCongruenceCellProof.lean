module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceCellProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalContextInsertion OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsCongruence
open OriginalHereditaryDeletionRowsCongruenceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ownBound (count : OTerm alpha) :
 Nonempty (Derivation body Delta (Below count (suc count))) := by
 apply actualOriginalOrderIntroduction body alpha Delta count (suc count) z
 rw [onEquality]
 exact ⟨trans (addSucc count z) (congSuc (addZero count))⟩

theorem increaseBound (index count : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Below index count))) :
 Nonempty (Derivation body Delta (Below index (suc count))) := by
 apply orderCases Delta index count _ h
 intro beta rho Theta gap hrho he
 simp only [Below,orderRename,sucRelabel]
 obtain ⟨he⟩ := he
 apply actualOriginalOrderIntroduction body beta Theta (index.relabel rho) (suc (count.relabel rho)) (suc gap)
 rw [onEquality]
 exact ⟨trans (addSucc (index.relabel rho) (suc gap)) (congSuc he)⟩

theorem restrict (Q : Program 2) (count input parameter other otherParameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (CellAgreement Q (suc count) input parameter other otherParameter))) :
 Nonempty (Derivation body Delta (CellAgreement Q count input parameter other otherParameter)) := by
 unfold CellAgreement
 apply actualFiniteUniversalIntroduction body alpha 3 Delta
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let x := input.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let p := parameter.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let y := other.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let q := otherParameter.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let i : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let a : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let b : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := cellFields Q c x p y q i a b
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hr := renameInto hc Sum.inl Theta (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 simp only [cellRename,sucRelabel] at hr
 have hb := increaseBound i c (andLeft hh)
 obtain ⟨he⟩ := cellApply Q (suc c) x p y q i a b hr (andIntro hb (andRight hh))
 simpa only [cellBody] using (Nonempty.intro (Derivation.implicationIntroduction he))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceCellProof
