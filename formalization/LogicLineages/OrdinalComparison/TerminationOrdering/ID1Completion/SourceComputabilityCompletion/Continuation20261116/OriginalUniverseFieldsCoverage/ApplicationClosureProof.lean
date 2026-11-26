module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BinaryResultObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

open InternalAdditionLawsProof (add)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

open InternalOriginalOrderSyntaxProof (addRelabel)

theorem atChildren (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw typ left right leftType rightType lv ls ll rv rs rl : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw typ left right)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hleft : Nonempty (Derivation body Delta (result n false left
      (ChildFrameProof.frame xs leftType (xs 6) (xs 7) lv ls ll))))
    (hright : Nonempty (Derivation body Delta (result n false right
      (ChildFrameProof.frame xs rightType (xs 6) (xs 7) rv rs rl)))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  apply BinaryResultObservationsProof.cases (suc (add ls rs)) ll rl _
  intro beta j Theta maximum canonical hj hmax hk
  simp only [sucRelabel,addRelabel] at hk
  rw [ResultSyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  have hlbj := renameInto hlb j Theta hj
  have hlpj := renameInto hlp j Theta hj
  have hrbj := renameInto hrb j Theta hj
  have hrpj := renameInto hrp j Theta hj
  have hleftj := renameInto hleft j Theta hj
  have hrightj := renameInto hright j Theta hj
  rw [graph3Rename] at hcj
  rw [ResultSyntaxProof.observationsRename] at hoj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj hlbj hlpj hrbj hrpj
  rw [ResultSyntaxProof.resultRename,ChildFrameSyntaxProof.frameRename] at hleftj hrightj
  exact ApplicationCoreProof.atValues n arity H (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j)
    (leftType.relabel j) (rightType.relabel j) (lv.relabel j) (ls.relabel j) (ll.relabel j)
    (rv.relabel j) (rs.relabel j) (rl.relabel j) maximum canonical (fun i => (xs i).relabel j)
    hcj hoj hmj hlbj hlpj hrbj hrpj hmax hk hleftj hrightj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ApplicationClosureProof
