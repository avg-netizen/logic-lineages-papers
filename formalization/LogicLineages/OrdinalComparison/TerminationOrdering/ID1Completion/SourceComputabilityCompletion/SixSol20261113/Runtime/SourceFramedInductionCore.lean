module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAtWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof (outputTransport)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalPositiveUnfoldingSupportProof (weakenClosed)
open InternalSourceInversionSupportProof (onEquality)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open OriginalHereditaryInternalAgendaSyntaxProof (jobRename)
open OriginalTypedDecoderInternalBranchProof (orCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceFramedDefinitions SourceFramedSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem successorAtJob (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound job weight : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowCompletion R H M W c B bound)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (hlt : Nonempty (Derivation body Delta (ltF weight (suc bound)))) :
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 obtain ⟨hs⟩ := InternalLeastNumberProof.actualRightSuccessorSplit body alpha weight bound
 change Derivation body [] ((ltF weight (suc bound)).imp
   (ltF weight bound ⊔ arithmeticEmbedding.onFormula (weight.equal bound))) at hs
 rw [onEquality] at hs
 obtain ⟨hlt⟩ := hlt
 have hc : Nonempty (Derivation body Delta (ltF weight bound ⊔ eqn weight bound)) :=
   ⟨Derivation.implicationElimination (weakenClosed hs Delta) hlt⟩
 apply orCases hc
 · let A := ltF weight bound
   exact belowApply R H M W c B bound job weight (withHyp hb A) (withHyp hj A) (withHyp hw A)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 · let A := eqn weight bound
   have hweight := outputTransport OriginalHereditaryFuelProgram.weight weight bound (Fin.cons job Fin.elim0)
     ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hw A)
   exact SourceFramedAtWeightProof.atWeight R H M W c B job bound (withHyp hb A) (withHyp hj A) hweight

theorem zeroRow (R : Program 2) (H : Program 1) (M W : Program 2) (c B : OTerm alpha) :
 Nonempty (Derivation body Delta (BelowCompletion R H M W c B z)) := by
 unfold BelowCompletion
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold belowMatrix
 simp only [zRelabel]
 let job : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let weight : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := OriginalHereditaryInternalAgenda.Job H M W (c.relabel Sum.inl) (B.relabel Sum.inl) job ⊓
   (graph1 OriginalHereditaryFuelProgram.weight weight job ⊓ ltF weight z)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 have hA : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body (alpha ⊕ Fin 2) weight
 obtain ⟨hlt⟩ := andRight (andRight hA)
 have hf := Derivation.implicationElimination (weakenClosed hn Theta) hlt
 exact ⟨Derivation.implicationIntroduction (Derivation.explosion hf)⟩

theorem succRow (R : Program 2) (H : Program 1) (M W : Program 2) (c B bound : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowCompletion R H M W c B bound))) :
 Nonempty (Derivation body Delta (BelowCompletion R H M W c B (suc bound))) := by
 unfold BelowCompletion
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold belowMatrix
 simp only [sucRelabel]
 let job : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let weight : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := OriginalHereditaryInternalAgenda.Job H M W (c.relabel Sum.inl) (B.relabel Sum.inl) job ⊓
   (graph1 OriginalHereditaryFuelProgram.weight weight job ⊓ ltF weight (suc (bound.relabel Sum.inl)))
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 have hi : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 2) ∈ Theta :=
   fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
 have hb' := renameInto hb Sum.inl Theta hi
 rw [belowRename] at hb'
 have hA : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := successorAtJob R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (bound.relabel Sum.inl) job weight
   hb' (andLeft hA) (andLeft (andRight hA)) (andRight (andRight hA))
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedInductionCore
