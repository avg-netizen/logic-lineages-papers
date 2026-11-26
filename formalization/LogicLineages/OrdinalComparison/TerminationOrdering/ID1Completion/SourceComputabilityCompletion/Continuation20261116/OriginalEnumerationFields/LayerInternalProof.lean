module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def payload (n : Nat) : Program 3 :=
  both (.composition (OriginalCodeValidityGuard.check n) ![raw]) (choose n)

theorem atPayload (n : Nat) (key answers param value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph3 (payload n) value key answers param))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc value) key answers param)) :=
  unaryValue .succ (payload n) (suc value) value ![key,answers,param]
    (successorValue (Fin.cons value Fin.elim0)) hp

theorem layerNonzero (n : Nat) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (key answers param out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) out key answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply programCases (payload n) (Fin.cons key (Fin.cons answers (Fin.cons param Fin.elim0)))
  intro beta j Theta value hj hp
  simp only [consTermRename,emptyRename] at hp
  change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
  rw [eqnRelabel,zRelabel]
  have hoj := renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  have hv := atPayload n (key.relabel j) (answers.relabel j) (param.relabel j) value hp
  have he := valueUnique (layer n) (out.relabel j) (suc value)
    ![key.relabel j,answers.relabel j,param.relabel j] hoj hv
  obtain ⟨he⟩ := withHyp he (eqn (out.relabel j) z)
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm he) (Derivation.hypothesis List.mem_cons_self)))⟩

theorem rankAt (key code bound param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound))) :
    Nonempty (Derivation body Delta (graph2 rank code key param)) :=
  unaryValue InternalUnpair.left (.projection 0) code key ![key,param]
    (pairLeft key code bound hk) (projectionValue 0 ![key,param])

theorem rankEqual (key code bound param out : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hr : Nonempty (Derivation body Delta (graph2 rank out key param))) :
    Nonempty (Derivation body Delta (eqn out code)) :=
  valueUnique rank out code ![key,param] hr (rankAt key code bound param hk)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
