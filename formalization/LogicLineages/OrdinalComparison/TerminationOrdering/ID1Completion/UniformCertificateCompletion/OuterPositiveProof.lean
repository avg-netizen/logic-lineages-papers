module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open GuardedSourceGraphSupportProof GammaGuardedSourceGraphSupportProof
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Reinsert BOTH original Gamma checks and the original typed endpoint
guard, on the supplied objects and certificate. The common Gamma is an
arbitrary object-language term, never a fixed meta-level environment. -/
theorem positiveAccept (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (context : Nat) (typ f g witness gammaCode x y parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode g)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (hpair : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (htf : Nonempty (Derivation body Delta (typedAccepted data x typ parameter)))
    (htg : Nonempty (Derivation body Delta (typedAccepted data y typ parameter)))
    (hp : Nonempty (Derivation body Delta
      (graph4 (Outer.rawPositive data oldStep bottom measure) (suc z) x y witness parameter))) :
    Nonempty (Derivation body Delta
      (certificate (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
        false context f g witness)) := by
  let positiveRaw := Outer.rawPositive data oldStep bottom measure
  let typed := GammaGuardedSource.baseTyped (Outer.typed data window oldComp.typed) Outer.valid
  let positive := GammaGuardedSource.basePositive
    (Outer.positive positiveRaw window oldSrc.positive) Outer.gamma
  let xs : Fin 4 → OTerm α :=
    Fin.cons (numeral context) (Fin.cons f (Fin.cons g (Fin.cons witness Fin.elim0)))
  have htagF := OuterTypedProof.tagValue data context typ f x parameter hx htf
  have htagG := OuterTypedProof.tagValue data context typ g y parameter hy htg
  have htypedF := OuterTypedProof.baseTypedAccept oldComp data window context typ f gammaCode x parameter
    hw hf hx hpair htf
  have htypedG := OuterTypedProof.baseTypedAccept oldComp data window context typ g gammaCode y parameter
    hw hg hy hpair htg
  have hpositive : Nonempty (Derivation body Delta (programGraph positive (suc z) xs)) :=
    conjunctionAccept (Outer.positive positiveRaw window oldSrc.positive)
      (GammaGuardedSource.sameGamma Outer.gamma 1 2) xs
      (OuterPositiveRawProof.dispatchAccept positiveRaw oldSrc.positive window context
        f g witness gammaCode x y parameter hw hf hg hx hy hpair hp)
      (sameGammaAccept Outer.gamma 1 2 gammaCode gammaCode xs hf hg ⟨refl gammaCode⟩)
  have hactive : Nonempty (Derivation body Delta
      (programGraph (GuardedSource.activation typed Outer.tag window) (suc z) xs)) :=
    conjunctionAccept (GuardedSource.windowAt window) (GuardedSource.sourceTyped typed Outer.tag) xs
      (windowAtAccept window (numeral context) f g witness hw)
      (sourceTypedAccept typed Outer.tag typ (numeral context) f g witness htagF htypedF)
  have htarget : Nonempty (Derivation body Delta
      (programGraph (GuardedSource.targetTyped typed Outer.tag) (suc z) xs)) := by
    apply compositionValue typed
      (Fin.cons (.projection 0) (Fin.cons (GuardedSource.rightTag Outer.tag)
        (Fin.cons (.projection 2) Fin.elim0))) (suc z) xs
      (Fin.cons (numeral context) (Fin.cons typ (Fin.cons g Fin.elim0))) htypedG
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (rightTagValue Outer.tag typ (numeral context) f g witness htagG)
        (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) i
  have hsame : Nonempty (Derivation body Delta
      (programGraph (GuardedSource.sameTag Outer.tag) (suc z) xs)) := by
    apply compositionValue InternalEqualityTest.equalityTest
      (Fin.cons (GuardedSource.leftTag Outer.tag) (Fin.cons (GuardedSource.rightTag Outer.tag) Fin.elim0))
      (suc z) xs (Fin.cons typ (Fin.cons typ Fin.elim0))
      (InternalEqualityTestCompositionProof.equalityOfEqual typ typ ⟨refl typ⟩)
    intro i
    exact Fin.cases (leftTagValue Outer.tag typ (numeral context) f g witness htagF)
      (Fin.cases (rightTagValue Outer.tag typ (numeral context) f g witness htagG)
        (fun q => Fin.elim0 q)) i
  exact successorBranchIntro (GuardedSource.activation typed Outer.tag window)
    positive (GuardedSource.acceptedTarget positive typed Outer.tag) (suc z) z xs hactive
    (conjunctionAccept positive
      (InternalAcceptance.conjunction (GuardedSource.targetTyped typed Outer.tag) (GuardedSource.sameTag Outer.tag))
      xs hpositive (conjunctionAccept _ _ xs htarget hsame))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveProof
