module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedFinalErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One original certificate, accepted by the retained raw leaf AND by the
literal original guarded step at the same final Data and effective oldStep.
The extra raw-leaf fact supports recursive prefix construction. -/
def Certificate {alpha : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha) : Formula alpha :=
  graph4 rawLeaf (numeral 1) s t cert parameter ⊓
    UniformCertificateCompletion.stepAccepted D oldStep s t cert parameter

def WitnessMatrix {alpha : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  Certificate D oldStep rawLeaf (s.relabel Sum.inl) (t.relabel Sum.inl)
    (.var (.inr 0)) (parameter.relabel Sum.inl)

def Witness {alpha : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha) : Formula alpha :=
  existsOne (WitnessMatrix D oldStep rawLeaf s t parameter)

/-- Collapse keeps strict rank decrease between the ORIGINAL endpoints.
Noncollapse binds one certificate and retains both original acceptance facts. -/
def Result {alpha : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter oldS oldT : OTerm alpha) : Formula alpha :=
  (equal s t ⊓ OriginalExistentialRankResultDefinitions.RankWitness oldS oldT) ⊔
    Witness D oldStep rawLeaf s t parameter

def Premise {alpha : Type} (source : Program 2) (leaf : Program 4)
    (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha) : Formula alpha :=
  graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf)
      (numeral 1) s t cert oldParam ⊓
    (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing oldParam c extended ⊓
    (graph2 InternalPairing.pairing newParam c gamma ⊓
    (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓
      graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t))))

/-- SAME actual prepared active-kernel final tuple, with no supplied
transformed recognition, validity, type guard, endpoint or normalization law.
The recognized INPUT restriction is explicit and remains unchanged. -/
def SameFinalGuardedErasure (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let D := Integration.preparedKernelFinalData p H G W P
  let leaf := (Integration.preparedKernelFinalInputs p H G W P).oldStep
  let source := InternalOriginalUniformDescentSelection.validity D
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha),
    Nonempty (Derivation body Delta
      ((Premise source leaf s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT).imp
        (graph2 source (numeral 1) erasedS newParam ⊓
          (graph2 source (numeral 1) erasedT newParam ⊓
            Result D leaf leaf erasedS erasedT newParam s t))))

def ActualSameFinalGuardedErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    SameFinalGuardedErasure p H G W P
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureTargets
