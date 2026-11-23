module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountOpenConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCountTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (valueUnique)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (trans symm congSuc addZero)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open NumberedWindowInternalLiteralCount (entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountOpenConsProof (chosenHead otherHead)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem added (left right head tail rest query lc rc tc sc bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (hl : Nonempty (Derivation body Delta (counted left query lc)))
    (hr : Nonempty (Derivation body Delta (counted right query rc)))
    (ht : Nonempty (Derivation body Delta (counted tail query tc)))
    (hs : Nonempty (Derivation body Delta (counted rest query sc)))
    (he : Nonempty (Derivation body Delta (eqn tc (OrdinaryArithmetic.addTerm sc bit)))) :
    Nonempty (Derivation body Delta (eqn lc (OrdinaryArithmetic.addTerm rc bit))) := by
  apply formulaCases (eqn head query)
  · have hq : Nonempty (Derivation body ((eqn head query) :: Delta) (eqn head query)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hvl := chosenHead left head tail query tc
      (withHyp hlc _) (withHyp ht _) hq
    have hvr := chosenHead right head rest query sc
      (withHyp hrc _) (withHyp hs _) hq
    obtain ⟨el⟩ := valueUnique entryCount lc (suc tc) ![left,query] (withHyp hl _) hvl
    obtain ⟨er⟩ := valueUnique entryCount rc (suc sc) ![right,query] (withHyp hr _) hvr
    obtain ⟨et⟩ := withHyp he (eqn head query)
    have ar := InternalOriginalOrderProof.congAddRight bit er
    have ea : Derivation body ((eqn head query) :: Delta)
        (eqn (OrdinaryArithmetic.addTerm (suc sc) bit) (suc (OrdinaryArithmetic.addTerm sc bit))) :=
      InternalAdditionLawsProof.leftSuccessor sc bit
    exact ⟨trans (trans el (congSuc et)) (symm (trans ar ea))⟩
  · have hq : Nonempty (Derivation body ((eqn head query).not :: Delta) (eqn head query).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hvl := otherHead left head tail query tc
      (withHyp hlc _) (withHyp ht _) hq
    have hvr := otherHead right head rest query sc
      (withHyp hrc _) (withHyp hs _) hq
    obtain ⟨el⟩ := valueUnique entryCount lc tc ![left,query] (withHyp hl _) hvl
    obtain ⟨er⟩ := valueUnique entryCount rc sc ![right,query] (withHyp hr _) hvr
    obtain ⟨et⟩ := withHyp he (eqn head query).not
    exact ⟨trans (trans el et) (symm (InternalOriginalOrderProof.congAddRight bit er))⟩

theorem equal (left right head tail rest query lc rc tc sc : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (hl : Nonempty (Derivation body Delta (counted left query lc)))
    (hr : Nonempty (Derivation body Delta (counted right query rc)))
    (ht : Nonempty (Derivation body Delta (counted tail query tc)))
    (hs : Nonempty (Derivation body Delta (counted rest query sc)))
    (he : Nonempty (Derivation body Delta (eqn tc sc))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  obtain ⟨he⟩ := he
  obtain ⟨d⟩ := added left right head tail rest query lc rc tc sc z hlc hrc hl hr ht hs
    ⟨trans he (symm (addZero sc))⟩
  exact ⟨trans d (addZero rc)⟩

/-- The literal pointwise effect of the original one-occurrence eraser. -/
def delta {alpha : Type} (needle query before after bit : OTerm alpha) : Formula alpha :=
  ((eqn needle query).imp (eqn before (OrdinaryArithmetic.addTerm after bit))) ⊓
    ((eqn needle query).not.imp (eqn before after))

/-- Retaining the same physical head on both original lists transports the
exact one-query tail effect, with its flag, to their full literal counts. -/
theorem liftEffect (left right head tail rest needle query lc rc tc sc bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (hl : Nonempty (Derivation body Delta (counted left query lc)))
    (hr : Nonempty (Derivation body Delta (counted right query rc)))
    (ht : Nonempty (Derivation body Delta (counted tail query tc)))
    (hs : Nonempty (Derivation body Delta (counted rest query sc)))
    (ih : Nonempty (Derivation body Delta (delta needle query tc sc bit))) :
    Nonempty (Derivation body Delta (delta needle query lc rc bit)) := by
  let E := eqn needle query
  have hy : Nonempty (Derivation body (E :: Delta) (eqn lc (OrdinaryArithmetic.addTerm rc bit))) := by
    obtain ⟨d⟩ := withHyp ih E
    have q : Derivation body (E :: Delta) E := Derivation.hypothesis List.mem_cons_self
    exact added left right head tail rest query lc rc tc sc bit
      (withHyp hlc E) (withHyp hrc E) (withHyp hl E) (withHyp hr E) (withHyp ht E) (withHyp hs E)
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft d) q⟩
  have hn : Nonempty (Derivation body (E.not :: Delta) (eqn lc rc)) := by
    obtain ⟨d⟩ := withHyp ih E.not
    have q : Derivation body (E.not :: Delta) E.not := Derivation.hypothesis List.mem_cons_self
    exact equal left right head tail rest query lc rc tc sc
      (withHyp hlc E.not) (withHyp hrc E.not) (withHyp hl E.not) (withHyp hr E.not)
      (withHyp ht E.not) (withHyp hs E.not)
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight d) q⟩
  obtain ⟨y⟩ := hy
  obtain ⟨n⟩ := hn
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction y)
    (Derivation.implicationIntroduction n)⟩

#print axioms liftEffect
#print axioms added
#print axioms equal
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCountTransportProof
