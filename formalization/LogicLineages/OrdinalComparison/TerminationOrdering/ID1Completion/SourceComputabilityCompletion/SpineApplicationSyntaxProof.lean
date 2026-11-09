module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldConsumerProof InternalParameterizedCanonicalResultFoldOpeningProof
open InternalOriginalUniformApplicationTypingApplicationProof
open InternalTagArithmeticSyntaxProof (OTerm z suc sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SpineApplicationTargets (selectedData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def premises (data : Data) (window : Program 1)
    (arrow d e f a out parameter fm flag depth next : OTerm α) : Formula α :=
  graph2 (BottomRepresentative.windowAt window) (suc z) f parameter ⊓
    (InternalOriginalUniformApplicationTyping.applicationPremises (selectedData data window)
        arrow d e f a out parameter ⊓
      (BottomSpineMeasure.graph fm f ⊓
        (graph1 InternalUnpair.left flag fm ⊓
          (graph1 InternalUnpair.right depth fm ⊓ graph1 Program.succ next depth))))

theorem premisesRename {β : Type} (data : Data) (window : Program 1)
    (arrow d e f a out parameter fm flag depth next : OTerm α) (j : α → β) :
    (premises data window arrow d e f a out parameter fm flag depth next).relabel j =
      premises data window (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j)
        (a.relabel j) (out.relabel j) (parameter.relabel j) (fm.relabel j)
        (flag.relabel j) (depth.relabel j) (next.relabel j) := by
  simp only [premises,conjunctionRename,graph2Rename,sucRelabel,zRelabel,
    applicationPremisesRename,BottomSpineMeasure.graph,graph1Rename]

theorem chainIff (P Q R : Formula α)
    (hpq : Nonempty (Derivation body Gamma (P.iff Q)))
    (hqr : Nonempty (Derivation body Gamma (Q.iff R))) :
    Nonempty (Derivation body Gamma (P.iff R)) := by
  obtain ⟨hpq'⟩ := withHyp hpq P
  obtain ⟨hqr'⟩ := withHyp hqr P
  have hf := Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionLeft hqr')
      (Derivation.implicationElimination (Derivation.conjunctionLeft hpq')
        (Derivation.hypothesis List.mem_cons_self)))
  obtain ⟨hpq''⟩ := withHyp hpq R
  obtain ⟨hqr''⟩ := withHyp hqr R
  have hb := Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionRight hpq'')
      (Derivation.implicationElimination (Derivation.conjunctionRight hqr'')
        (Derivation.hypothesis List.mem_cons_self)))
  exact ⟨Derivation.conjunctionIntroduction hf hb⟩


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
