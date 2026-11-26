module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NumberedMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open MeaningSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem forward (n : Nat) (bound fuel types heads labels tupleBound prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.numberedCase n labels heads types tupleBound prior raw))) :
    Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) := by
  apply OriginalEnumerationLayerFields.NumberedSyntaxProof.cases n labels heads types tupleBound prior raw _ h
  intro beta j Theta ys hj hf
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel]
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hctor := andRight hf
  have h9 := andLeft hf
  have hx := andRight h9
  have h8 := andLeft h9
  have hall := andRight h8
  have h7 := andLeft h8
  have hlenBound := andRight h7
  have h6 := andLeft h7
  have hlen := andRight h6
  have h5 := andLeft h6
  have hb := andRight h5
  have h4 := andLeft h5
  have ht := andRight h4
  have h3 := andLeft h4
  have hconvert := andRight h3
  have h2 := andLeft h3
  have hhead := andRight h2
  have hlabel := andLeft h2
  have hbm := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 4) hij).mp hb
  have hxm := (ListBindingProof.atRaw n (prior.relabel j) (bound.relabel j) (fuel.relabel j)
    (types.relabel j) (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 6) hij).mp hx
  have hh := OriginalEncodedNumberedEnumerationBranch.MapImageProof.introduce (OriginalEncodedHeadConversion.convert n)
    (heads.relabel j) (ys 2) (ys 1) hhead hconvert
  have htypes := OriginalEnumerationFields.Types.AllowedProof.introduce (ys 5) (types.relabel j)
    (tupleBound.relabel j) (ys 7) hlen hlenBound hall
  exact (NumberedMeaningProof.numbered n (raw.relabel j) (bound.relabel j) (fuel.relabel j) (types.relabel j)
    (heads.relabel j) (labels.relabel j) (tupleBound.relabel j) (ys 0) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) hctor).mpr
    (andIntro hvj (andIntro (andIntro (andIntro (andIntro (andIntro hlabel hh) ht) hbm) htypes) hxm))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.LayerNumberedProof
