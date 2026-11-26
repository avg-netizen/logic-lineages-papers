module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadAllowedProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem recover (n : Nat) (heads mapped rawHead : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (convertedHeads n) mapped heads)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) mapped rawHead))) :
    Nonempty (Derivation body Delta (Targets.headAllowed n heads rawHead)) :=
  MapElimProof.recover (OriginalEncodedHeadConversion.convert n) heads mapped rawHead hv hm

theorem introduce (n : Nat) (heads mapped rawHead : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (convertedHeads n) mapped heads)))
    (hm : Nonempty (Derivation body Delta (Targets.headAllowed n heads rawHead))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) mapped rawHead)) := by
  apply MapImageEliminationProof.cases (OriginalEncodedHeadConversion.convert n) heads rawHead _ hm
  intro beta j Theta source hj hmember hconvert
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hvj := renameInto hv j Theta hj
  rw [graph1Rename] at hvj
  exact MapIntroProof.introduce (OriginalEncodedHeadConversion.convert n) (heads.relabel j) z
    (mapped.relabel j) (rawHead.relabel j) z source hvj hmember hconvert
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadAllowedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadAllowedProof
