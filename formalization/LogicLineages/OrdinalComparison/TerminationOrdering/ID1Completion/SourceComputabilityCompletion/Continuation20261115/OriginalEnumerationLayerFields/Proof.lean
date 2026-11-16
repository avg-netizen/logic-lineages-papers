module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.AssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n) out xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (Targets.alternatives n xs code)) := by
  have hw := (OriginalEnumerationConstructorLayer.StatementChecks.exactMembership body alpha Delta n xs out code hg).mp hm
  apply InternalFiniteBlocksProof.elimination body alpha 8 Delta
    (OriginalEnumerationConstructorLayer.Targets.witnessMatrix n xs code) _ hw
  let j : alpha → alpha ⊕ Fin 8 := Sum.inl
  let ys : Fin 8 → OTerm (alpha ⊕ Fin 8) := fun i => .var (.inr i)
  let Theta := OriginalEnumerationConstructorLayer.Targets.witnessMatrix n xs code :: Delta.map (fun q => q.relabel j)
  have hf : Nonempty (Derivation body Theta (OriginalEnumerationConstructorLayer.Targets.witnessMatrix n xs code)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  rw [AssemblyProof.alternativesRename]
  exact AssemblyProof.forward n (fun i => (xs i).relabel j) ys (code.relabel j) (andLeft hf) (andRight hf)

theorem backward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n) out xs)))
    (hw : Nonempty (Derivation body Delta (Targets.alternatives n xs code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (OriginalEnumerationConstructorLayer.components n) xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hwj := InternalGraphCompositionFunctionalityProof.renameInto hw j Theta hj
  rw [AssemblyProof.alternativesRename] at hwj
  have hc : Nonempty (Derivation body Theta (OriginalEnumerationConstructorLayer.Targets.componentGraphs n
      (fun i => (xs i).relabel j) ys)) :=
    andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (hq 0) (hq 1)) (hq 2)) (hq 3)) (hq 4)) (hq 5)) (hq 6)) (hq 7)
  exact OriginalEnumerationConstructorLayer.ObservationsProof.atComponents n (fun i => (xs i).relabel j) ys
    (out.relabel j) (code.relabel j) hgj hc
    (AssemblyProof.backward n (fun i => (xs i).relabel j) ys (code.relabel j) hc hwj)

theorem internalLayerFields : Targets.InternalLayerFields := by
  intro body alpha Delta n xs out code hg
  constructor
  · exact forward n xs out code hg
  · exact backward n xs out code hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Proof
