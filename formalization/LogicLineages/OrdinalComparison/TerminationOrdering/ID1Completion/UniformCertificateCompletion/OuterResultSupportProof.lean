module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationStepPeel (graph5)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationGraphProof InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem applicationActivation (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (sigma tau : Ty) (f a : OTerm α)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (hd : Nonempty (Derivation body Delta
      (domain (Outer.computability old data window oldVertex oldResult) context sigma tau f a))) :
    Nonempty (Derivation body Delta
      (graph5 (Outer.resultActivation old data window) (suc z) (numeral context)
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) f a)) := by
  exact ApplicationGuardedActivationProof.activationAt window
    (Outer.baseComputability old data window).typed (Outer.baseComputability old data window).guard
    Outer.arrow (numeral context) (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (numeral (typeNumber (.arrow sigma tau))) f a
    (GuardedSourceCertificateProof.windowNumeral window context hw)
    (ApplicationGuardedActivationProof.arrowNumeral Outer.arrow sigma tau (OuterArithmeticProof.arrowEvaluation sigma tau))
    (andLeft (andLeft hd)) (andRight (andLeft hd)) (andRight hd)

/-- Invert the two literal ORIGINAL active branches: the application
checker first, then the complete result builder. No output typing or
coordinate property is assumed. -/
theorem resultBranchRecover (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (sigma tau : Ty) (f a out : OTerm α)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (hd : Nonempty (Derivation body Delta
      (domain (Outer.computability old data window oldVertex oldResult) context sigma tau f a)))
    (ha : Nonempty (Derivation body Delta
      (accepted (Outer.computability old data window oldVertex oldResult) sigma tau
        (numeral context) f a out))) :
    Nonempty (Derivation body Delta
      (graph5 (Outer.resultBranch (Path.vertex data window oldVertex)) out (numeral context)
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) f a)) := by
  let xs : Fin 5 → OTerm α := Fin.cons (numeral context)
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons f (Fin.cons a Fin.elim0))))
  have hc := applicationActivation old data window oldVertex oldResult context sigma tau f a hw hd
  have hr := activeRecover (Outer.resultActivation old data window)
    (Outer.result old data window oldVertex oldResult) old.application xs out hc ha
  exact successorBranchElim (Outer.resultActivation old data window) oldResult
    (Outer.resultBranch (Path.vertex data window oldVertex)) out z xs hc hr

/-- At actual raw coordinate graphs the supplied result is literally the
original pair of the function Gamma and supplied raw vertex output. -/
theorem resultPair (vertex : Program 5) (context : Nat) (sigma tau : Ty)
    (f a out gammaCode x argument parameter value : OTerm α)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument a)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hv : Nonempty (Derivation body Delta
      (graph5 vertex value parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument x)))
    (hr : Nonempty (Derivation body Delta
      (graph5 (Outer.resultBranch vertex) out (numeral context)
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) f a))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out gammaCode value)) := by
  let xs : Fin 5 → OTerm α := Fin.cons (numeral context)
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons f (Fin.cons a Fin.elim0))))
  let vp : Program 5 := .composition vertex
    (Fin.cons (Outer.parameter (.projection 0) (.projection 3))
      (Fin.cons (.projection 1) (Fin.cons (.projection 2)
        (Fin.cons (rightOf (.projection 4)) (Fin.cons (rightOf (.projection 3)) Fin.elim0)))))
  have hleft := unaryValue InternalUnpair.left (.projection (3 : Fin 5)) gammaCode f xs
    hf (projectionValue 3 xs)
  have hrightF := unaryValue InternalUnpair.right (.projection (3 : Fin 5)) x f xs
    hx (projectionValue 3 xs)
  have hrightA := unaryValue InternalUnpair.right (.projection (4 : Fin 5)) argument a xs
    ha (projectionValue 4 xs)
  have hparameter := OuterCarrierSupportProof.parameterValue (.projection (0 : Fin 5)) (.projection 3)
    (numeral context) f gammaCode parameter xs (projectionValue 0 xs) (projectionValue 3 xs) hf hp
  have hvertex : Nonempty (Derivation body Delta (programGraph vp value xs)) := by
    apply compositionValue vertex _ value xs
      (Fin.cons parameter (Fin.cons (numeral (typeNumber sigma))
        (Fin.cons (numeral (typeNumber tau)) (Fin.cons argument (Fin.cons x Fin.elim0))))) hv
    intro i
    exact Fin.cases hparameter (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases hrightA (Fin.cases hrightF (fun j => Fin.elim0 j))))) i
  exact binaryRecover InternalPairing.pairing (leftOf (.projection (3 : Fin 5))) vp
    out gammaCode value xs hr hleft hvertex

theorem outputCoordinates (out gammaCode value : OTerm α)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out gammaCode value))) :
    Nonempty (Derivation body Delta
      (graph1 InternalUnpair.left gammaCode out ⊓ graph1 InternalUnpair.right value out)) := by
  obtain ⟨rule⟩ := InternalUnpairProof.actualOriginalGeneratedCodeInverse body α out gammaCode value
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (weakenClosed rule Delta) hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultSupportProof
