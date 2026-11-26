module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionInstances
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionBase
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
open FramedContentInductionDefinitions FramedContentInductionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow (R : Program 2) (H : Program 1) (M W : Program 2) (c B : OTerm alpha) :
 Nonempty (Derivation body Delta (BelowContent R H M W c B z)) := by
 unfold BelowContent
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionBase
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionBase
