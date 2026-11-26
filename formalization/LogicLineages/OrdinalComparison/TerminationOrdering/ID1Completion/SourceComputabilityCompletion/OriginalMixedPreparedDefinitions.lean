module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPrepared
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def concrete (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
 OriginalTransparentDecoderSelection.transparentInputs H G W p
def bottom (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
 OriginalTransparentDirectBottom.refineInputs (concrete p H G W)
def prepared (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
 OriginalTransparentMixedPathDefinitions.refineInputs (bottom p H G W)
def member (p : GlobalSourcePackage.Inputs) : Program 2 :=
 InternalOriginalUniformContextMembership.contextMember p.base.member

/-- Literal pre-selection checker identity, not equality to any later final checker. -/
def Literal (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
 (prepared p H G W).base.oldSource = OriginalTransparentMixedDirectBottom.source H G (member p) W ∧
 (prepared p H G W).oldStep = OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep

/-- The checked restricted trace theorem at exactly the prepared checker and original source. No later final leaf is named. -/
def Trace (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop := ∀
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (prepared p H G W).base.oldSource (numeral 1) s oldParam ⊓
   (graph4 (prepared p H G W).oldStep (numeral 1) s t cert oldParam ⊓
   (graph4 (OriginalMixedDirectBottomTrace.recognizes (prepared p H G W).base.oldSource (prepared p H G W).oldStep) (numeral 1) s t cert oldParam ⊓
   (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
   (graph2 InternalPairing.pairing oldParam c extended ⊓
   (graph2 InternalPairing.pairing newParam c gamma ⊓
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
    graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))))).imp
   (graph2 (prepared p H G W).base.oldSource (numeral 1) erasedS newParam ⊓
    OriginalExistentialRankResultDefinitions.Result (prepared p H G W).oldStep erasedS erasedT newParam s t)))

def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
 GlobalSourcePackage.InputsCalibrated n arity (prepared p H G W) ∧
 (∀ v : List.Vector Nat 4, evaluate (prepared p H G W).oldStep v = evaluate p.oldStep v) ∧
 Literal p H G W ∧
 OriginalActiveKernelMinimum.Properties n arity (prepared p H G W) H G W P ∧
 Trace p H G W
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPrepared
