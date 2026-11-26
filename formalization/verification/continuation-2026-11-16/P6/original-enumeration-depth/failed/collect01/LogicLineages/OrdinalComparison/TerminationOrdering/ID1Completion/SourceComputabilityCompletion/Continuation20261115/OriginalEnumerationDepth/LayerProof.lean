module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def childMaximum : Program 3 := .composition collect (fun _ : Fin 1 => .projection 1)
def payload : Program 3 := .composition .succ (fun _ : Fin 1 => childMaximum)
def successful : Program 3 := .composition .succ (fun _ : Fin 1 => payload)

theorem acceptedValue (n : Nat) (raw answers param out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) out raw))) :
    Nonempty (Derivation body Delta (graph3 (accepted n) out raw answers param)) :=
  unaryValue (OriginalCodeValidityGuard.check n) (.projection 0) out raw ![raw,answers,param] hg (projectionValue 0 ![raw,answers,param])

theorem zeroValue (n : Nat) (raw answers param : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc z) raw answers param)) :=
  zeroBranchIntro (accepted n) (OriginalRawSyntaxTransport.constant 3 1) successful
    (suc z) ![raw,answers,param] (acceptedValue n raw answers param z hg)
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 ![raw,answers,param])

theorem positiveValue (n : Nat) (raw answers param value : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hc : Nonempty (Derivation body Delta (graph1 collect value answers))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc (suc value)) raw answers param)) := by
  have hm : Nonempty (Derivation body Delta (graph3 childMaximum value raw answers param)) :=
    unaryValue collect (.projection 1) value answers ![raw,answers,param] hc (projectionValue 1 ![raw,answers,param])
  have hp : Nonempty (Derivation body Delta (graph3 payload (suc value) raw answers param)) :=
    unaryValue .succ childMaximum (suc value) value ![raw,answers,param] (successorValue (Fin.cons value Fin.elim0)) hm
  have hs : Nonempty (Derivation body Delta (graph3 successful (suc (suc value)) raw answers param)) :=
    unaryValue .succ payload (suc (suc value)) (suc value) ![raw,answers,param] (successorValue (Fin.cons (suc value) Fin.elim0)) hp
  exact successorBranchIntro (accepted n) (OriginalRawSyntaxTransport.constant 3 1) successful
    (suc (suc value)) z ![raw,answers,param] (acceptedValue n raw answers param (suc z) hg) hs

theorem fromSuccess (n : Nat) (raw answers param out value : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param)))
    (hv : Nonempty (Derivation body Delta (graph3 (layer n) (suc value) raw answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  have he := valueUnique (layer n) out (suc value) ![raw,answers,param] ho hv
  obtain ⟨he⟩ := withHyp he (eqn out z)
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm he) (Derivation.hypothesis List.mem_cons_self)))⟩

theorem positiveNonzero (n : Nat) (raw answers param out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply programCases collect (Fin.cons answers Fin.elim0) _
  intro beta j Theta value hj hc
  change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hc
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  exact fromSuccess n (raw.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) (suc value) hoj
    (positiveValue n (raw.relabel j) (answers.relabel j) (param.relabel j) value hgj hc)

theorem layerNonzero (n : Nat) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw answers param out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply OriginalCodeBoundsRecursion.CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
    rw [eqnRelabel,zRelabel]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    exact fromSuccess n (raw.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) z hoj
      (zeroValue n (raw.relabel j) (answers.relabel j) (param.relabel j) hg)
  · intro beta j Theta hj hg
    change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
    rw [eqnRelabel,zRelabel]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    exact positiveNonzero n (raw.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) hg hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.LayerProof
