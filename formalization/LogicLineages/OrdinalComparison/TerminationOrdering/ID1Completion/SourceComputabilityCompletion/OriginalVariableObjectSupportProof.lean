module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterWindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSupportProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableObject OriginalVariableObjectSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (OTerm emb z suc)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- The read-only Object observer opens to the exact original raw variable
test at the supplied actual right-coordinate graph. -/
theorem variablePayloadRecover (object payload : OTerm α)
    (hv : Nonempty (Derivation body Delta (variableObject object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object))) :
    Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one payload)) :=
  unaryRecover OriginalConstructorLeaf.variableTest InternalUnpair.right
    InternalOriginalStepGuard.one payload (Fin.cons object Fin.elim0) hv hr

/-- Both original selector graphs reconstruct the target Object, then the
literal bottom payload graph builds its original two-input constructor. -/
theorem bottomObjectAccept (object gammaCode payload typeCode : OTerm α)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode object)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload object)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode payload typeCode))) :
    Nonempty (Derivation body Delta (ComputabilityLeast.bottomGraph object typeCode gammaCode)) := by
  let xs : Fin 2 → OTerm α := Fin.cons typeCode (Fin.cons gammaCode Fin.elim0)
  have hp := reconstructPair object gammaCode payload hg hr
  exact binaryValue InternalPairing.pairing (.projection (1 : Fin 2))
    (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => .projection 0))
    object gammaCode payload xs hp (projectionValue 1 xs)
    (unaryValue BottomRepresentative.bottomCode (.projection (0 : Fin 2)) payload typeCode xs
      hb (projectionValue 0 xs))

theorem bottomAtSourceGammaIntroduction (tau : Ty) (source target gammaCode : OTerm α)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode source)))
    (hb : Nonempty (Derivation body Delta
      (ComputabilityLeast.bottomGraph target
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gammaCode))) :
    Nonempty (Derivation body Delta (bottomAtSourceGamma tau source target)) := by
  obtain ⟨hg⟩ := hg
  obtain ⟨hb⟩ := hb
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb gammaCode)
  rw [bottomAtSourceGammaInstance]
  exact Derivation.conjunctionIntroduction hg hb

/-- Eliminate the internally bound original Gamma coordinate. No decoded
ambient context, re-encoding equation or external witness is supplied. -/
theorem bottomAtSourceGammaCases (tau : Ty) (source target : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Delta (bottomAtSourceGamma tau source target)))
    (k : ∀ (β : Type) (j : α → β) (Theta : List (Formula β)) (gammaCode : OTerm β),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.left gammaCode (source.relabel j))) →
      Nonempty (Derivation body Theta
        (ComputabilityLeast.bottomGraph (target.relabel j)
          (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gammaCode)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  let P := graph1 InternalUnpair.left (.var (.inr (0 : Fin 1))) (source.relabel Sum.inl) ⊓
    ComputabilityLeast.bottomGraph (target.relabel Sum.inl)
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) (.var (.inr 0))
  let Theta := P :: Delta.map weaken
  have hh : Derivation body Theta P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft hh⟩ ⟨Derivation.conjunctionRight hh⟩
  exact ⟨Derivation.existentialElimination h d⟩

/-- Strip only the two natively redundant guards around the original whole
positive checker. Its original endpoints, raw path code and parameter stay
unchanged. -/
theorem positiveRecover (data : InternalOriginalUniformDescentSelection.Data)
    (oldStep : Program 4) (bottom measure : Program 1)
    (x y witness parameter : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (graph4 (Outer.rawPositive data oldStep bottom measure) (suc z) x y witness parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
        x y witness parameter)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons x (Fin.cons y (Fin.cons witness (Fin.cons parameter Fin.elim0)))
  have h := conjunctionRecover (PositiveGuard.nonBottomGuard bottom)
    (InternalAcceptance.conjunction (PositiveGuard.spineGuard measure)
      (InternalParameterizedPathChecker.checker (edgeChecker data oldStep) true)) xs hp
  have h' := conjunctionRecover (PositiveGuard.spineGuard measure)
    (InternalParameterizedPathChecker.checker (edgeChecker data oldStep) true) xs (andRight h)
  exact andRight h'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSupportProof
