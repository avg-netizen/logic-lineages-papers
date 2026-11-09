module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
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

theorem dispatchRecover (positiveRaw oldPositive : Program 4) (window : Program 1)
    (context : Nat) (f g witness gammaCode x y parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (hpair : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hp : Nonempty (Derivation body Delta
      (graph4 (Outer.positive positiveRaw window oldPositive) (suc z) (numeral context) f g witness))) :
    Nonempty (Derivation body Delta (graph4 positiveRaw (suc z) x y witness parameter)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons (numeral context) (Fin.cons f (Fin.cons g (Fin.cons witness Fin.elim0)))
  have hbranch := successorBranchElim (Outer.windowAt window (0 : Fin 4)) oldPositive
    (Outer.positiveBranch positiveRaw) (suc z) z xs
    (OuterCarrierSupportProof.windowValue window 0 xs hw) hp
  have hc := conjunctionRecover (GammaGuardedSource.sameGamma Outer.gamma 1 2)
    (.composition positiveRaw
      (Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
        (Fin.cons (.projection 3) (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0)))))
    xs hbranch
  have hrightF := unaryValue InternalUnpair.right (.projection (1 : Fin 4)) x f xs
    hx (projectionValue 1 xs)
  have hrightG := unaryValue InternalUnpair.right (.projection (2 : Fin 4)) y g xs
    hy (projectionValue 2 xs)
  have hparameter := OuterCarrierSupportProof.parameterValue (.projection (0 : Fin 4)) (.projection 1)
    (numeral context) f gammaCode parameter xs (projectionValue 0 xs) (projectionValue 1 xs) hf hpair
  apply compositionRecover positiveRaw
    (Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
      (Fin.cons (.projection 3) (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0))))
    (suc z) xs (Fin.cons x (Fin.cons y (Fin.cons witness (Fin.cons parameter Fin.elim0)))) (andRight hc)
  intro i
  exact Fin.cases hrightF (Fin.cases hrightG
    (Fin.cases (projectionValue 3 xs) (Fin.cases hparameter (fun j => Fin.elim0 j)))) i

theorem dispatchAccept (positiveRaw oldPositive : Program 4) (window : Program 1)
    (context : Nat) (f g witness gammaCode x y parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode g)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (hpair : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hp : Nonempty (Derivation body Delta (graph4 positiveRaw (suc z) x y witness parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (Outer.positive positiveRaw window oldPositive) (suc z) (numeral context) f g witness)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons (numeral context) (Fin.cons f (Fin.cons g (Fin.cons witness Fin.elim0)))
  have hrightF := unaryValue InternalUnpair.right (.projection (1 : Fin 4)) x f xs
    hx (projectionValue 1 xs)
  have hrightG := unaryValue InternalUnpair.right (.projection (2 : Fin 4)) y g xs
    hy (projectionValue 2 xs)
  have hparameter := OuterCarrierSupportProof.parameterValue (.projection (0 : Fin 4)) (.projection 1)
    (numeral context) f gammaCode parameter xs (projectionValue 0 xs) (projectionValue 1 xs) hf hpair
  have hraw : Nonempty (Derivation body Delta
      (programGraph (.composition positiveRaw
        (Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
          (Fin.cons (.projection 3) (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0)))))
        (suc z) xs)) := by
    apply compositionValue positiveRaw
      (Fin.cons (rightOf (.projection 1)) (Fin.cons (rightOf (.projection 2))
        (Fin.cons (.projection 3) (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0))))
      (suc z) xs (Fin.cons x (Fin.cons y (Fin.cons witness (Fin.cons parameter Fin.elim0)))) hp
    intro i
    exact Fin.cases hrightF (Fin.cases hrightG
      (Fin.cases (projectionValue 3 xs) (Fin.cases hparameter (fun j => Fin.elim0 j)))) i
  have hsame := sameGammaAccept Outer.gamma 1 2 gammaCode gammaCode xs hf hg ⟨refl gammaCode⟩
  have hbranch := conjunctionAccept (GammaGuardedSource.sameGamma Outer.gamma 1 2) _ xs hsame hraw
  exact successorBranchIntro (Outer.windowAt window (0 : Fin 4)) oldPositive
    (Outer.positiveBranch positiveRaw) (suc z) z xs
    (OuterCarrierSupportProof.windowValue window 0 xs hw) hbranch

theorem rawPositiveRecover (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (data : Data) (rawScalar : Program 2) (oldStep : Program 4) (bottom measure window : Program 1)
    (context : Nat) (f g witness gammaCode x y parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.right y g)))
    (hpair : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hp : Nonempty (Derivation body Delta
      (certificate (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window)
        false context f g witness))) :
    Nonempty (Derivation body Delta
      (graph4 (Outer.rawPositive data oldStep bottom measure) (suc z) x y witness parameter)) := by
  let positiveRaw := Outer.rawPositive data oldStep bottom measure
  let positive := Outer.positive positiveRaw window oldSrc.positive
  let typed := GammaGuardedSource.baseTyped (Outer.typed data window oldComp.typed) Outer.valid
  let xs : Fin 4 → OTerm α :=
    Fin.cons (numeral context) (Fin.cons f (Fin.cons g (Fin.cons witness Fin.elim0)))
  have hb := GammaGuardedSourceBranchProof.guardedPositiveRecover
    (GammaGuardedSource.basePositive positive Outer.gamma) typed Outer.tag window xs hp
  have hc := conjunctionRecover positive (GammaGuardedSource.sameGamma Outer.gamma 1 2) xs hb
  exact dispatchRecover positiveRaw oldSrc.positive window context f g witness gammaCode x y parameter
    hw hf hx hy hpair (andLeft hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
