module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldRecoverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm)

theorem remove (weight : Program 1) (list head tail needle rest total tailSum restSum needleWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (ho : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hs : Nonempty (Derivation body Delta (eqn tailSum restSum))) :
    Nonempty (Derivation body Delta (graph2 merge total needleWeight restSum)) := by
  obtain ⟨he'⟩ := he
  have hh := headTransport weight needleWeight needle head Fin.elim0 ⟨symm he'⟩ hw
  have hm := FoldRecoverProof.cons weight list head tail tailSum needleWeight total hc ht hh ho
  exact TransportBaseProof.secondTransport merge total needleWeight tailSum restSum hs hm

theorem keepAbsent (weight : Program 1) (list head tail kept rest total tailSum restSum headWeight remainingSum : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (ho : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingSum kept)))
    (he : Nonempty (Derivation body Delta (eqn tailSum restSum))) :
    Nonempty (Derivation body Delta (eqn total remainingSum)) := by
  have hl := FoldRecoverProof.cons weight list head tail tailSum headWeight total hc ht hw ho
  have hright := FoldRecoverProof.cons weight kept head rest restSum headWeight remainingSum hk hs hw hr
  have hleft := TransportBaseProof.secondTransport merge total headWeight tailSum restSum he hl
  exact valueUnique merge total remainingSum ![headWeight,restSum] hleft hright

theorem keepFound (weight : Program 1) (list head tail kept rest total tailSum restSum headWeight needleWeight remainingSum : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (ho : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingSum kept)))
    (he : Nonempty (Derivation body Delta (graph2 merge tailSum needleWeight restSum))) :
    Nonempty (Derivation body Delta (graph2 merge total needleWeight remainingSum)) := by
  have hl := FoldRecoverProof.cons weight list head tail tailSum headWeight total hc ht hw ho
  have hright := FoldRecoverProof.cons weight kept head rest restSum headWeight remainingSum hk hs hw hr
  apply InternalAcceptanceSupportProof.programCases merge ![needleWeight,remainingSum] _
  intro beta j Theta out hj hm
  have hx : (fun i => (![needleWeight,remainingSum] i).relabel j) = ![needleWeight.relabel j,remainingSum.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hm
  rw [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename]
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hright j Theta hj
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  rw [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename] at hlj hrj hej
  obtain ⟨heq⟩ := MergeInterchangeProof.interchange (headWeight.relabel j) (needleWeight.relabel j)
    (restSum.relabel j) (tailSum.relabel j) (remainingSum.relabel j) (total.relabel j) out hej hrj hlj hm
  exact outputTransport merge out (total.relabel j) ![needleWeight.relabel j,remainingSum.relabel j] ⟨symm heq⟩ hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedEraseValueProof
