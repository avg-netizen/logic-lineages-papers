module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerAcceptanceProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalTagArithmeticSupportProof (cancelSuc)
open InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem positiveValue (n : Nat) (key code bound answers param value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) code)))
    (hc : Nonempty (Derivation body Delta (graph3 (choose n) value key answers param))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc value) key answers param)) := by
  apply LayerInternalProof.atPayload n key answers param value
  exact successorBranchIntro _ _ _ value z ![key,answers,param]
    (LayerGuardProof.guardAt n key code bound answers param (suc z) hk hg) hc

theorem positiveRecover (n : Nat) (key code bound answers param value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) code)))
    (hl : Nonempty (Derivation body Delta (graph3 (layer n) (suc value) key answers param))) :
    Nonempty (Derivation body Delta (graph3 (choose n) value key answers param)) := by
  apply programCases (LayerInternalProof.payload n) (Fin.cons key (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta inner hj hp
  simp only [consTermRename,emptyRename] at hp
  rw [graph3Rename]
  have hkj := renameInto hk j Theta hj
  have hgj := renameInto hg j Theta hj
  have hlj := renameInto hl j Theta hj
  rw [graph2Rename] at hkj
  simp only [graph1Rename,sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hgj
  simp only [graph3Rename,sucRelabel] at hlj
  have hs := LayerInternalProof.atPayload n (key.relabel j) (answers.relabel j) (param.relabel j) inner hp
  obtain ⟨he⟩ := valueUnique (layer n) (suc inner) (suc (value.relabel j))
    ![key.relabel j,answers.relabel j,param.relabel j] hs hlj
  have hv := outputTransport (LayerInternalProof.payload n) inner (value.relabel j)
    ![key.relabel j,answers.relabel j,param.relabel j] ⟨cancelSuc he⟩ hp
  exact successorBranchElim _ _ _ (value.relabel j) z ![key.relabel j,answers.relabel j,param.relabel j]
    (LayerGuardProof.guardAt n (key.relabel j) (code.relabel j) (bound.relabel j) (answers.relabel j) (param.relabel j) (suc z) hkj hgj) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerAcceptanceProof
