module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountOpenConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseHeadCountProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalListCodecSupportProof (consGraph)
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (symm trans congSuc addZero addSucc)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalControlGraphSupportProof (headTransport valueUnique)
open NumberedWindowInternalLiteralCount (entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountOpenConsProof (chosenHead otherHead)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseCoordinatesProof (chosenHeadCoordinates)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

private theorem tapeTwo (c n : OTerm alpha) :
    (![c,n] : Fin 2 → OTerm alpha) = Fin.cons c (Fin.cons n Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

/-- Exact local count-effect branch: when deletion of the actual head has
returned the actual cons tail, each literal query sees one removed occurrence
if equal to the erased needle and an unchanged count otherwise. -/
theorem atHeadCounts (raw head tail needle remaining query before after : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph raw head tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hrem : Nonempty (Derivation body Delta (eqn remaining tail)))
    (hbefore : Nonempty (Derivation body Delta (counted raw query before)))
    (hafter : Nonempty (Derivation body Delta (counted remaining query after))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn before (OrdinaryArithmetic.addTerm after (suc z)))) ⊓
       ((eqn needle query).not.imp (eqn before after)))) := by
  have hrun : Nonempty (Derivation body Delta
      (programGraph entryCount after (Fin.cons remaining (Fin.cons query Fin.elim0)))) := by
    simpa only [counted,tapeTwo] using hafter
  have htail : Nonempty (Derivation body Delta (counted tail query after)) := by
    simpa only [counted,tapeTwo] using
      (headTransport entryCount after remaining tail (Fin.cons query Fin.elim0) hrem hrun)
  let E := eqn needle query
  have hyes : Nonempty (Derivation body (E :: Delta) (eqn before (OrdinaryArithmetic.addTerm after (suc z)))) := by
    obtain ⟨eh⟩ := withHyp he E
    have en : Derivation body (E :: Delta) E := Derivation.hypothesis List.mem_cons_self
    have hv := chosenHead raw head tail query after (withHyp hc E) (withHyp htail E) ⟨trans eh en⟩
    obtain ⟨d⟩ := valueUnique entryCount before (suc after) ![raw,query] (withHyp hbefore E) hv
    have plus : Derivation body (E :: Delta) (eqn (OrdinaryArithmetic.addTerm after (suc z)) (suc after)) :=
      trans (addSucc after z) (congSuc (addZero after))
    exact ⟨trans d (symm plus)⟩
  have hno : Nonempty (Derivation body (E.not :: Delta) (eqn before after)) := by
    let H := eqn head query
    have no : Nonempty (Derivation body (E.not :: Delta) H.not) := by
      obtain ⟨eh⟩ := withHyp (withHyp he E.not) H
      have yes : Derivation body (H :: E.not :: Delta) H := Derivation.hypothesis List.mem_cons_self
      have nn : Derivation body (H :: E.not :: Delta) E.not :=
        Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination nn (trans (symm eh) yes))⟩
    have hv := otherHead raw head tail query after (withHyp hc E.not) (withHyp htail E.not) no
    exact valueUnique entryCount before after ![raw,query] (withHyp hbefore E.not) hv
  obtain ⟨hyes⟩ := hyes
  obtain ⟨hno⟩ := hno
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hyes)
    (Derivation.implicationIntroduction hno)⟩

/-- The matching-head branch of the actual state gives this count relation
when its zero-flag child state still contains the physical original tail. -/
theorem actualHeadCounts (raw head tail needle child canon acc bit remaining query before after : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph raw head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state child tail needle)))
    (hp0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child z tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hcanon : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canon (suc z) tail)))
    (hstate : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit remaining)))
    (hbefore : Nonempty (Derivation body Delta (counted raw query before)))
    (hafter : Nonempty (Derivation body Delta (counted remaining query after))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn before (OrdinaryArithmetic.addTerm after (suc z)))) ⊓
       ((eqn needle query).not.imp (eqn before after)))) := by
  obtain ⟨d⟩ := chosenHeadCoordinates raw head tail needle child tail canon acc bit remaining hc ht hp0 he hcanon hstate hpair
  exact atHeadCounts raw head tail needle remaining query before after hc he
    ⟨Derivation.conjunctionRight d⟩ hbefore hafter

#print axioms atHeadCounts
#print axioms actualHeadCounts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseHeadCountProof
