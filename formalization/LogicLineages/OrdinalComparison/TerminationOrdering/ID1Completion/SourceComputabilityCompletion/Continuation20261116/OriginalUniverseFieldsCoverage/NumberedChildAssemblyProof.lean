module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedChildAssemblyProof
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

theorem atValues (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw rootLabel head typ left types right leftType lv ls ll rv rs rl childLabel maximum canonical : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hh : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n (xs 4) head)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) typ)))
    (hlb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hlp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hrb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hrp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm0 : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum childLabel ll rl)))
    (hm1 : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum rootLabel childLabel)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc (add ls rs)) maximum)))
    (hal : Nonempty (Derivation body Delta (accepted n arity H true leftType left (xs 6) (xs 2))))
    (har : Nonempty (Derivation body Delta (accepted n arity H true types right (xs 6) (xs 2))))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hlength := ObservationPartsProof.length n arity H false _ _ ho
  have hlf := ChildFrameProof.child n arity H false true raw left
    leftType (xs 6) (xs 7) lv ls ll
    xs ho hal hlength hlb hlp
  have hrf := ChildFrameProof.child n arity H false true raw right
    types (xs 6) (xs 7) rv rs rl
    xs ho har hlength hrb hrp
  have hd := OriginalTypedEnumerationDepthBound.DescentProof.numbered raw rootLabel
    head typ left types right hc
  have hil := ChildInductionProof.atChild n arity H true raw left _ ih (andLeft hd) hlf
  have hir := ChildInductionProof.atChild n arity H true raw right _ ih (andRight hd) hrf
  exact NumberedCoreProof.atValues n arity H raw rootLabel head typ
    left types right leftType
    lv ls ll rv rs rl childLabel maximum canonical
    xs hc ho hh hv hm hlb hlp hrb hrp hm0 hm1 hk hil hir

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedChildAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.NumberedChildAssemblyProof
