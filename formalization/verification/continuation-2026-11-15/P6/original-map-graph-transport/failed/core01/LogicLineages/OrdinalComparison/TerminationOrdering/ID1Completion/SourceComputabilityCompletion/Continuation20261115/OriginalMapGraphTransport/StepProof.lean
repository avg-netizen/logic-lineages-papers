module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open ExchangeMapGraph
open Targets AgreementSyntaxProof AgreementBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem missing (key rest left right out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 lookup z left key)))
    (hr : Nonempty (Derivation body Delta (graph2 lookup z right key)))
    (hs : Nonempty (Derivation body Delta (graph3 mapStep out key rest left))) :
    Nonempty (Derivation body Delta (graph3 mapStep out key rest right)) := by
  have hleft := ExchangeMapGraph.InternalProof.mapMissingStep key rest left hl
  have he := valueUnique mapStep rest out ![key,rest,left] hleft hs
  exact outputTransport mapStep rest out ![key,rest,right] he
    (ExchangeMapGraph.InternalProof.mapMissingStep key rest right hr)

theorem presentAt (key rest left right out value code : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 lookup (suc value) left key)))
    (hr : Nonempty (Derivation body Delta (graph2 lookup (suc value) right key)))
    (hs : Nonempty (Derivation body Delta (graph3 mapStep out key rest left)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code value rest))) :
    Nonempty (Derivation body Delta (graph3 mapStep out key rest right)) := by
  have hleft := ArgumentEntriesConsTable.MapProof.presentStep key left value rest code hl hc
  have he := valueUnique mapStep code out ![key,rest,left] hleft hs
  exact outputTransport mapStep code out ![key,rest,right] he
    (ArgumentEntriesConsTable.MapProof.presentStep key right value rest code hr hc)

theorem present (key rest left right out value : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 lookup (suc value) left key)))
    (hr : Nonempty (Derivation body Delta (graph2 lookup (suc value) right key)))
    (hs : Nonempty (Derivation body Delta (graph3 mapStep out key rest left))) :
    Nonempty (Derivation body Delta (graph3 mapStep out key rest right)) := by
  apply programCases InternalListCodec.consCode (Fin.cons value (Fin.cons rest Fin.elim0)) _
  intro beta j Theta code hj hc
  simp only [consTermRename,emptyRename] at hc
  rw [graph3Rename]
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,sucRelabel] at hlj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,sucRelabel] at hrj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  rw [graph3Rename] at hsj
  exact presentAt (key.relabel j) (rest.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) (value.relabel j) code hlj hrj hsj hc

theorem atValue (key rest left right out value : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 lookup value left key)))
    (hr : Nonempty (Derivation body Delta (graph2 lookup value right key)))
    (hs : Nonempty (Derivation body Delta (graph3 mapStep out key rest left))) :
    Nonempty (Derivation body Delta (graph3 mapStep out key rest right)) := by
  apply zeroSuccessorCases Delta value _
  · exact missing key rest left right out
      (outputTransport lookup value z ![left,key] ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hl (eqn value z)))
      (outputTransport lookup value z ![right,key] ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hr (eqn value z)))
      (withHyp hs (eqn value z))
  · intro beta j Theta val hj he
    rw [graph3Rename]
    have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
    rw [graph2Rename] at hlj
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    rw [graph2Rename] at hrj
    have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
    rw [graph3Rename] at hsj
    exact present (key.relabel j) (rest.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) val
      (outputTransport lookup (value.relabel j) (suc val) ![left.relabel j,key.relabel j] he hlj)
      (outputTransport lookup (value.relabel j) (suc val) ![right.relabel j,key.relabel j] he hrj) hsj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.StepProof
