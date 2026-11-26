module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsStepAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EntryBounds EntryBoundsBindingProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (cancelSuc symm)
open InternalApplicationStepPeelSupportProof (andIntro andRight)
open Continuation20261114 Continuation20261115

theorem atValues (n : Nat) (raw typ head tail param entries value tailEntries entry listCode tailValue headValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hf : Nonempty (Derivation body Delta (graph1 (Fold.weighted (Fold.entryWeight n)) value entries)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (htf : Nonempty (Derivation body Delta (graph1 (Fold.weighted (Fold.entryWeight n)) tailValue tailEntries)))
    (hh : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) headValue head)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) value raw)) := by
  have hgood := EntryGuardProof.children n raw typ head tail hc hg
  have hsmall := andRight (OriginalTypedEnumerationDepthBound.DescentProof.cons raw typ head tail hc)
  have htail := belowRawApply n raw tail param tailEntries tailValue ih hsmall
    (andIntro (andRight hgood) (andIntro ht htf))
  have hextract := StandaloneConsExtraction.Proof.consSuccess body alpha Delta raw typ head tail param tailEntries entry listCode hc ht hp hl
  obtain ⟨heq⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) (suc listCode) ![raw,param] he hextract
  have heq' : Nonempty (Derivation body Delta (eqn entries listCode)) := ⟨cancelSuc heq⟩
  have hfold := headTransport (Fold.weighted (Fold.entryWeight n)) value entries listCode Fin.elim0 heq' hf
  have hw := FoldValueProof.entry n entry typ head headValue hp hh
  have hm := FoldRecoverProof.cons (Fold.entryWeight n) listCode entry tailEntries tailValue headValue value hl htf hw hfold
  exact EntryBoundsConsProof.cons n raw typ head tail headValue tailValue value hc hg hh htail hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsStepAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsStepAtProof
