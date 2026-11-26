module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ActiveDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof FactsProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationCertificateConstructorsSupportProof
theorem reversed (n : Nat) (arity : Fin n → Nat)
    (left right node rev window symbols types : OTerm alpha)
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply OriginalDecodedRank.SupportProof.pairCases left _
  intro beta j Theta st sp hj hl
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hh := h.rename j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  apply OriginalDecodedRank.SupportProof.pairCases (right.relabel j) _
  intro gamma k Xi tt tp hk hr
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hh' := hh.rename k Xi hk
  have ihk := renameInto ihj k Xi hk
  rw [belowRawRename] at ihk
  have hlk := renameInto hl k Xi hk
  rw [graph2Rename] at hlk
  have hs := OriginalDecodedSuccessShape.CoreProof.successShape n arity
    ((node.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    (st.relabel k) (sp.relabel k) tt tp ((window.relabel j).relabel k) hh'.pair hlk hr hh'.exchange
  exact ActiveDispatchProof.reversed n arity ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    ((node.relabel j).relabel k) ((rev.relabel j).relabel k) ((window.relabel j).relabel k)
    ((symbols.relabel j).relabel k) ((types.relabel j).relabel k) (st.relabel k) tt
    (pairLeft _ _ _ hlk) (pairLeft _ _ _ hr) (andLeft hs) (andRight hs) hh' ihk

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.StepProof
