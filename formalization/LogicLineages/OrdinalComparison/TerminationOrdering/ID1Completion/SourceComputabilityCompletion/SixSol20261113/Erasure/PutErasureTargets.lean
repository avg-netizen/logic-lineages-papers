module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutIntegrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal bytes commute with erasure, for ordinary sources. No validity,
recognition, successful transported step or child erasure is an input. -/
def ActualPutErasureCommutation : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t typ raw head base label d cutoff erasedS erasedT : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base ⊓
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label ⊓
      (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
        graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))).imp
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode erasedT erasedS label)))

def WitnessMatrix {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (s t parameter label : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  graph2 SixSol20261112.Erasure.PutRoot.certificateCode (.var (.inr 0))
      (s.relabel Sum.inl) (label.relabel Sum.inl) ⊓
    stepAccepted (PutIntegration.finalData p H G W P)
      (PutIntegration.finalInputs p H G W P).oldStep
      (s.relabel Sum.inl) (t.relabel Sum.inl) (.var (.inr 0)) (parameter.relabel Sum.inl)

def Witness {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (s t parameter label : OTerm alpha) : Formula alpha :=
  existsOne (WitnessMatrix p H G W P s t parameter label)

/-- Transport an actual literal PUT across insertion erasure at the same
prepared selected tuple. Derive transformed validity, ordinary shape, PUT
result and actual guarded W; no canonical fixedness or transformed acceptance
is assumed. This is not yet arbitrary original object-certificate erasure. -/
def ActualFinalPutErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert oldParam newParam typ raw head base label gamma extended d cutoff c erasedS erasedT : OTerm alpha),
  Nonempty (Derivation body Delta
    ((PutIntegration.Fields p H G W P s t cert oldParam typ raw head base label ⊓
      (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
      (graph2 InternalPairing.pairing oldParam c extended ⊓
      (graph2 InternalPairing.pairing newParam c gamma ⊓
      (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
        graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))).imp
      (graph2 (InternalOriginalUniformDescentSelection.validity (PutIntegration.finalData p H G W P))
          (numeral 1) erasedS newParam ⊓
        (graph2 (InternalOriginalUniformDescentSelection.validity (PutIntegration.finalData p H G W P))
          (numeral 1) erasedT newParam ⊓ Witness p H G W P erasedS erasedT newParam label))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasure
