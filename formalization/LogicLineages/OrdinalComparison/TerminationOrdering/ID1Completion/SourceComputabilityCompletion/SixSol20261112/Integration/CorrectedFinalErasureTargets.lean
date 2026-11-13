module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.ClosedTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.CorrectedTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual selected Data of precisely the final input tuple above. -/
def preparedKernelFinalData (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : InternalOriginalUniformDescentSelection.Data :=
  let f := preparedKernelFinalInputs p H G W P
  OuterSelection.data f.base f.window

/-- Restricted recognized erasure at the ACTUAL selected final source and
effective leaf of one original prepared active-kernel tuple. The transformed
certificate is accepted by that SAME final effective leaf. Source, path, input
Gamma and result rank refer to their original arithmetic definitions. -/
def FinalRecognizedErasure (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let D := preparedKernelFinalData p H G W P
  let leaf := (preparedKernelFinalInputs p H G W P).oldStep
  let source := InternalOriginalUniformDescentSelection.validity D
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf)
        (numeral 1) s t cert oldParam ⊓
      (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
      (graph2 InternalPairing.pairing oldParam c extended ⊓
      (graph2 InternalPairing.pairing newParam c gamma ⊓
      (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
        graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))).imp
      (graph2 source (numeral 1) erasedS newParam ⊓
        OriginalExistentialRankResultDefinitions.Result leaf erasedS erasedT newParam s t)))

def ActualPreparedKernelFinalErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    FinalRecognizedErasure p H G W P

/-- One tuple and all local compilers are chosen before every source window,
Gamma and internal Derivation. The entire accepted prepared package remains
literal; its actual final Data and oldStep are the ones used by erasure. -/
def ActualPreparedKernelFinalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    OriginalMixedPrepared.Properties n arity p H G W P ∧
      FinalRecognizedErasure p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
