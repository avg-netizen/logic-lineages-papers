module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NonzeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSupportProof InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def inner (n : Nat) : Program 2 := .composition OriginalBoundsRecombination.merge
  ![.composition (OriginalBoundsRecombination.root n) (fun _ : Fin 1 => .projection 0),
    .composition OriginalBoundsRecombination.collect (fun _ : Fin 1 => .projection 1)]

theorem fromSuccess (n : Nat) (raw answers param out value : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param)))
    (hv : Nonempty (Derivation body Delta (graph3 (layer n) (suc value) raw answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  have he := valueUnique (layer n) out (suc value) ![raw,answers,param] ho hv
  obtain ⟨he⟩ := withHyp he (eqn out z)
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm he) (Derivation.hypothesis List.mem_cons_self)))⟩

theorem positive (n : Nat) (raw answers param out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply programCases (inner n) (Fin.cons raw (Fin.cons answers Fin.elim0))
  intro beta j Theta value hj hv
  change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hv
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  have hr := SupportProof.recombineSuccess n (raw.relabel j) (answers.relabel j) value hgj hv
  have hl := SupportProof.positiveValue n (raw.relabel j) (answers.relabel j) (param.relabel j) (suc value) hgj hr
  exact fromSuccess n (raw.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) value hoj hl

theorem internalLayerNonzero : Targets.InternalLayerNonzero := by
  intro n body alpha Delta raw answers param out ho
  apply CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
    rw [eqnRelabel,zRelabel]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    exact fromSuccess n (raw.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) z hoj
      (SupportProof.zeroValue n (raw.relabel j) (answers.relabel j) (param.relabel j) hg)
  · intro beta j Theta hj hg
    change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
    rw [eqnRelabel,zRelabel]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    exact positive n (raw.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) hg hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NonzeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NonzeroProof
