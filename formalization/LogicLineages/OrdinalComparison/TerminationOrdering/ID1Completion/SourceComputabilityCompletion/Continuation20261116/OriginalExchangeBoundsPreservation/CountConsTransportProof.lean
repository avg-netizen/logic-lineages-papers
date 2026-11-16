module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountRemoveAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountConsTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (trans symm congSuc addZero)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem added (left right head tail rest query lc rc tc sc bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right query)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail query)))
    (hs : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count sc rest query)))
    (he : Nonempty (Derivation body Delta (eqn tc (OrdinaryArithmetic.addTerm sc bit)))) :
    Nonempty (Derivation body Delta (eqn lc (OrdinaryArithmetic.addTerm rc bit))) := by
  apply formulaCases (eqn head query)
  · have hq : Nonempty (Derivation body ((eqn head query) :: Delta) (eqn head query)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hvl := ArgumentEntryCount.InternalProof.internalEqualCons body alpha _ left head tail query tc
      (withHyp hlc _) (withHyp ht _) hq
    have hvr := ArgumentEntryCount.InternalProof.internalEqualCons body alpha _ right head rest query sc
      (withHyp hrc _) (withHyp hs _) hq
    obtain ⟨el⟩ := valueUnique ArgumentEntryCount.count lc (suc tc) ![left,query] (withHyp hl _) hvl
    obtain ⟨er⟩ := valueUnique ArgumentEntryCount.count rc (suc sc) ![right,query] (withHyp hr _) hvr
    obtain ⟨et⟩ := withHyp he (eqn head query)
    have ar := InternalOriginalOrderProof.congAddRight bit er
    have ea : Derivation body ((eqn head query) :: Delta)
        (eqn (OrdinaryArithmetic.addTerm (suc sc) bit) (suc (OrdinaryArithmetic.addTerm sc bit))) :=
      InternalAdditionLawsProof.leftSuccessor sc bit
    exact ⟨trans (trans el (congSuc et)) (symm (trans ar ea))⟩
  · have hq : Nonempty (Derivation body ((eqn head query).not :: Delta) (eqn head query).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hvl := ArgumentEntryCount.InternalProof.internalUnequalCons body alpha _ left head tail query tc
      (withHyp hlc _) (withHyp ht _) hq
    have hvr := ArgumentEntryCount.InternalProof.internalUnequalCons body alpha _ right head rest query sc
      (withHyp hrc _) (withHyp hs _) hq
    obtain ⟨el⟩ := valueUnique ArgumentEntryCount.count lc tc ![left,query] (withHyp hl _) hvl
    obtain ⟨er⟩ := valueUnique ArgumentEntryCount.count rc sc ![right,query] (withHyp hr _) hvr
    obtain ⟨et⟩ := withHyp he (eqn head query).not
    exact ⟨trans (trans el et) (symm (InternalOriginalOrderProof.congAddRight bit er))⟩

theorem equal (left right head tail rest query lc rc tc sc : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left query)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right query)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail query)))
    (hs : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count sc rest query)))
    (he : Nonempty (Derivation body Delta (eqn tc sc))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  obtain ⟨he⟩ := he
  obtain ⟨d⟩ := added left right head tail rest query lc rc tc sc z hlc hrc hl hr ht hs
    ⟨trans he (symm (addZero sc))⟩
  exact ⟨trans d (addZero rc)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountConsTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountConsTransportProof
