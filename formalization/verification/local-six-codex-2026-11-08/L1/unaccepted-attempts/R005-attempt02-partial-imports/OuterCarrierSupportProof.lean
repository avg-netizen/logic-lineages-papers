module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalAccessibilityRules
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionSyntaxProof InternalFiniteBlocksBindingProof
open GuardedSourceSyntaxProof SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (z suc sucSubst zSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem carrierGraph (src : SourcePresentation.Data) (odd : Bool) (context : Nat) (x : OTerm α) :
    carrier src odd context x = graph2 (carrierProgram src odd) (suc z) (numeral context) x := by
  unfold carrier SourcePresentation.checkerFormula
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

theorem windowValue {m : Nat} (window : Program 1) (i : Fin m) (xs : Fin m → OTerm α)
    (h : Nonempty (Derivation body Delta (graph1 window (suc z) (xs i)))) :
    Nonempty (Derivation body Delta (programGraph (Outer.windowAt window i) (suc z) xs)) :=
  unaryValue window (.projection i) (suc z) (xs i) xs h (projectionValue i xs)

theorem parameterValue {m : Nat} (context object : Program m)
    (c o gammaCode parameter : OTerm α) (xs : Fin m → OTerm α)
    (hc : Nonempty (Derivation body Delta (programGraph context c xs)))
    (ho : Nonempty (Derivation body Delta (programGraph object o xs)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode o)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gammaCode))) :
    Nonempty (Derivation body Delta (programGraph (Outer.parameter context object) parameter xs)) :=
  binaryValue InternalPairing.pairing context (leftOf object) parameter c gammaCode xs hp hc
    (unaryValue InternalUnpair.left object gammaCode o xs hg ho)

theorem parameterRecover {m : Nat} (context object : Program m)
    (c o gammaCode parameter : OTerm α) (xs : Fin m → OTerm α)
    (hc : Nonempty (Derivation body Delta (programGraph context c xs)))
    (ho : Nonempty (Derivation body Delta (programGraph object o xs)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode o)))
    (hp : Nonempty (Derivation body Delta (programGraph (Outer.parameter context object) parameter xs))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gammaCode)) :=
  binaryRecover InternalPairing.pairing context (leftOf object) parameter c gammaCode xs hp hc
    (unaryValue InternalUnpair.left object gammaCode o xs hg ho)

/-- Bind the original object coordinates and context/Gamma pair using
original Program totality. No Object or Context decoder premise is used. -/
theorem objectCases (context : Nat) (object : OTerm α) (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β) (gammaCode payload parameter : OTerm β)
      (Theta : List (Formula β)),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.left gammaCode (object.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right payload (object.relabel j))) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 3 → Program 2 :=
    Fin.cons (leftOf (.projection 1)) (Fin.cons (rightOf (.projection 1))
      (Fin.cons (Outer.parameter (.projection 0) (.projection 1)) Fin.elim0))
  apply queryCases qs (Fin.cons (numeral context) (Fin.cons object Fin.elim0)) psi
  intro β j ys Theta hj hq
  simp only [consTermRename,emptyRename,numeralRename] at hq
  let xs : Fin 2 → OTerm β := Fin.cons (numeral context) (Fin.cons (object.relabel j) Fin.elim0)
  have hg := unaryRecover InternalUnpair.left (.projection (1 : Fin 2)) (ys 0)
    (object.relabel j) xs (hq 0) (projectionValue 1 xs)
  have hr := unaryRecover InternalUnpair.right (.projection (1 : Fin 2)) (ys 1)
    (object.relabel j) xs (hq 1) (projectionValue 1 xs)
  have hp := parameterRecover (.projection (0 : Fin 2)) (.projection 1)
    (numeral context) (object.relabel j) (ys 0) (ys 2) xs
    (projectionValue 0 xs) (projectionValue 1 xs) hg (hq 2)
  exact h β j (ys 0) (ys 1) (ys 2) Theta hj hg hr hp

/-- Open the actual raw typed dispatch at one original symbolic p. All
object coordinates and the original pairing are genuine graph premises. -/
theorem typedDispatchRecover (data : Data) (window : Program 1) (oldTyped : Program 3)
    (context : Nat) (typ object gammaCode payload parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (ht : Nonempty (Derivation body Delta (graph3 (Outer.typed data window oldTyped) (suc z)
      (numeral context) typ object))) :
    Nonempty (Derivation body Delta (typedAccepted data payload typ parameter)) := by
  let xs : Fin 3 → OTerm α := Fin.cons (numeral context) (Fin.cons typ (Fin.cons object Fin.elim0))
  have hwindow := windowValue window (0 : Fin 3) xs hw
  have hbranch := successorBranchElim (Outer.windowAt window (0 : Fin 3)) oldTyped
    (Outer.typedBranch data) (suc z) z xs hwindow ht
  have hright := unaryValue InternalUnpair.right (.projection (2 : Fin 3)) payload object xs
    hr (projectionValue 2 xs)
  have hparameter := parameterValue (.projection (0 : Fin 3)) (.projection 2)
    (numeral context) object gammaCode parameter xs (projectionValue 0 xs) (projectionValue 2 xs) hg hp
  apply compositionRecover (InternalOriginalUniformDescentSelection.selectedTyped data)
    (Fin.cons (rightOf (.projection 2)) (Fin.cons (.projection 1)
      (Fin.cons (Outer.parameter (.projection 0) (.projection 2)) Fin.elim0))) (suc z) xs
    (Fin.cons payload (Fin.cons typ (Fin.cons parameter Fin.elim0))) hbranch
  intro i
  exact Fin.cases hright (Fin.cases (projectionValue 1 xs)
    (Fin.cases hparameter (fun j => Fin.elim0 j))) i

theorem typedRecover (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (typ object gammaCode payload parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (Outer.computability old data window oldVertex oldResult).typed (suc z)
        (numeral context) typ object))) :
    Nonempty (Derivation body Delta (typedAccepted data payload typ parameter)) := by
  let xs : Fin 3 → OTerm α := Fin.cons (numeral context) (Fin.cons typ (Fin.cons object Fin.elim0))
  change Nonempty (Derivation body Delta
    (programGraph (GuardedSource.guardedTyped
      (GammaGuardedSource.baseTyped (Outer.typed data window old.typed) Outer.valid) Outer.tag) (suc z) xs)) at ht
  have hb := conjunctionRecover
    (GammaGuardedSource.baseTyped (Outer.typed data window old.typed) Outer.valid)
    (GuardedSource.typedMatch Outer.tag) xs ht
  have hc := conjunctionRecover (Outer.typed data window old.typed)
    (GammaGuardedSource.atInput Outer.valid 2) xs (andLeft hb)
  exact typedDispatchRecover data window old.typed context typ object gammaCode payload parameter
    hw hg hr hp (andLeft hc)

/-- Rebuild the literal original object scalar checker from the SAME raw
payload/parameter checker. It does not infer any decoder or semantic fact. -/
theorem scalarAccept (rawScalar oldScalar : Program 2) (window : Program 1) (context : Nat)
    (object gammaCode payload parameter : OTerm α)
    (hw : Nonempty (Derivation body Delta (graph1 window (suc z) (numeral context))))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hs : Nonempty (Derivation body Delta (graph2 rawScalar (suc z) payload parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (Outer.scalar rawScalar window oldScalar) (suc z) (numeral context) object)) := by
  let xs : Fin 2 → OTerm α := Fin.cons (numeral context) (Fin.cons object Fin.elim0)
  have hright := unaryValue InternalUnpair.right (.projection (1 : Fin 2)) payload object xs
    hr (projectionValue 1 xs)
  have hparameter := parameterValue (.projection (0 : Fin 2)) (.projection 1)
    (numeral context) object gammaCode parameter xs (projectionValue 0 xs) (projectionValue 1 xs) hg hp
  have hbranch := binaryValue rawScalar (rightOf (.projection (1 : Fin 2)))
    (Outer.parameter (.projection 0) (.projection 1)) (suc z) payload parameter xs hs hright hparameter
  exact successorBranchIntro (Outer.windowAt window (0 : Fin 2)) oldScalar (Outer.scalarBranch rawScalar)
    (suc z) z xs (windowValue window (0 : Fin 2) xs hw) hbranch

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterCarrierSupportProof
