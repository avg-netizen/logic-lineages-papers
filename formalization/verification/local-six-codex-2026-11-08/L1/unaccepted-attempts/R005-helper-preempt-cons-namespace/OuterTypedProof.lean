module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open GuardedSourceGraphSupportProof GammaGuardedSourceGraphSupportProof
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem typedDispatchAccept (data : Data) (window : Program 1) (oldTyped : Program 3)
    (context : Nat) (typ object gammaCode payload parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (ht : Nonempty (Derivation body Delta (typedAccepted data payload typ parameter))) :
    Nonempty (Derivation body Delta (graph3 (Outer.typed data window oldTyped) (suc z)
      (numeral context) typ object)) := by
  let xs : Fin 3 → OTerm α := Fin.cons (numeral context) (Fin.cons typ (Fin.cons object Fin.elim0))
  have hright := unaryValue InternalUnpair.right (.projection (2 : Fin 3)) payload object xs
    hr (projectionValue 2 xs)
  have hparameter := OuterCarrierSupportProof.parameterValue (.projection (0 : Fin 3)) (.projection 2)
    (numeral context) object gammaCode parameter xs (projectionValue 0 xs) (projectionValue 2 xs) hg hp
  have hbranch : Nonempty (Derivation body Delta (programGraph (Outer.typedBranch data) (suc z) xs)) := by
    apply compositionValue (InternalOriginalUniformDescentSelection.selectedTyped data)
      (Fin.cons (rightOf (.projection 2)) (Fin.cons (.projection 1)
        (Fin.cons (Outer.parameter (.projection 0) (.projection 2)) Fin.elim0))) (suc z) xs
      (Fin.cons payload (Fin.cons typ (Fin.cons parameter Fin.elim0))) ht
    intro i
    exact Fin.cases hright (Fin.cases (projectionValue 1 xs)
      (Fin.cases hparameter (fun j => Fin.elim0 j))) i
  exact successorBranchIntro (Outer.windowAt window (0 : Fin 3)) oldTyped (Outer.typedBranch data)
    (suc z) z xs (OuterCarrierSupportProof.windowValue window 0 xs hw) hbranch

/-- The type tag is recovered from the SAME raw typed graph, rather than
from a semantic decoding theorem about the supplied object. -/
theorem tagValue (data : Data) (context : Nat) (typ object payload parameter : OTerm α)
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (ht : Nonempty (Derivation body Delta (typedAccepted data payload typ parameter))) :
    Nonempty (Derivation body Delta (graph2 Outer.tag typ (numeral context) object)) := by
  have factors := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (InternalOriginalUniformDescentSelection.validity data) data.member
    payload typ parameter ht
  let xs : Fin 2 → OTerm α := Fin.cons (numeral context) (Fin.cons object Fin.elim0)
  exact unaryValue InternalUnpair.left (rightOf (.projection (1 : Fin 2))) typ payload xs
    (andLeft (andRight (andRight factors)))
    (unaryValue InternalUnpair.right (.projection (1 : Fin 2)) payload object xs
      hr (projectionValue 1 xs))

theorem baseTypedAccept (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (context : Nat) (typ object gammaCode payload parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (ht : Nonempty (Derivation body Delta (typedAccepted data payload typ parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (GammaGuardedSource.baseTyped (Outer.typed data window old.typed) Outer.valid)
        (suc z) (numeral context) typ object)) := by
  let xs : Fin 3 → OTerm α := Fin.cons (numeral context) (Fin.cons typ (Fin.cons object Fin.elim0))
  exact conjunctionAccept _ _ xs
    (typedDispatchAccept data window old.typed context typ object gammaCode payload parameter hw hg hr hp ht)
    (atInputValue Outer.valid 2 (suc z) xs (InternalLessThanSupportProof.oneConstantValue ![object]))

theorem typedAccept (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat)
    (typ object gammaCode payload parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (ht : Nonempty (Derivation body Delta (typedAccepted data payload typ parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (Outer.computability old data window oldVertex oldResult).typed (suc z)
        (numeral context) typ object)) :=
  guardedTypedAccept _ _ typ (numeral context) typ object
    (tagValue data context typ object payload parameter hr ht)
    (baseTypedAccept old data window context typ object gammaCode payload parameter hw hg hr hp ht)
    ⟨refl typ⟩

theorem objectGuard (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (f a gammaCode : OTerm α)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode a))) :
    Nonempty (Derivation body Delta
      (guarded (Outer.computability old data window oldVertex oldResult) f a)) :=
  guardAccept Outer.valid Outer.gamma gammaCode gammaCode f a hf ha
    (InternalLessThanSupportProof.oneConstantValue ![f])
    (InternalLessThanSupportProof.oneConstantValue ![a]) ⟨refl gammaCode⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTypedProof
