module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCasesProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalComputabilityApplication InternalAccessibilityRules InternalComputabilityDownward
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof (graph1Rename graph2Rename)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalPositiveUnfoldingSupportProof GuardedSourceSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Open an actual accepted result without guessing its raw payload.
Original totality binds the actual raw vertex value, and the original pair
inverse derives BOTH coordinates of the supplied result object. -/
theorem resultCases (old : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (sigma tau : Ty)
    (f a out gammaCode x argument parameter : OTerm α)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (hf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode f)))
    (hx : Nonempty (Derivation body Delta (graph1 InternalUnpair.right x f)))
    (ha : Nonempty (Derivation body Delta (graph1 InternalUnpair.right argument a)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hd : Nonempty (Derivation body Delta
      (domain (Outer.computability old data window oldVertex oldResult) context sigma tau f a)))
    (haccepted : Nonempty (Derivation body Delta
      (accepted (Outer.computability old data window oldVertex oldResult) sigma tau
        (numeral context) f a out)))
    (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β) (value : OTerm β) (Theta : List (Formula β)),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph5 (Path.vertex data window oldVertex) value (parameter.relabel j)
          (numeral (typeNumber sigma)) (numeral (typeNumber tau)) (argument.relabel j) (x.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.left (gammaCode.relabel j) (out.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right value (out.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  have hr := OuterResultSupportProof.resultBranchRecover old data window oldVertex oldResult
    context sigma tau f a out hw hd haccepted
  let xs : Fin 5 → OTerm α := Fin.cons parameter
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons argument (Fin.cons x Fin.elim0))))
  apply programCases (Path.vertex data window oldVertex) xs psi
  intro β j Theta value hj hv
  simp only [consTermRename,emptyRename,numeralRename] at hv
  have hf' := renameInto hf j Theta hj
  have hx' := renameInto hx j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hf' hx' ha'
  rw [graph2Rename] at hp'
  rw [graph5Rename] at hr'
  simp only [numeralRename] at hp' hr'
  have hpair := OuterResultSupportProof.resultPair (Path.vertex data window oldVertex)
    context sigma tau (f.relabel j) (a.relabel j) (out.relabel j) (gammaCode.relabel j)
    (x.relabel j) (argument.relabel j) (parameter.relabel j) value hf' hx' ha' hp' hv hr'
  have hcoordinates := OuterResultSupportProof.outputCoordinates (out.relabel j) (gammaCode.relabel j) value hpair
  exact h β j value Theta hj hv (andLeft hcoordinates) (andRight hcoordinates)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCasesProof
