module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack InternalApplicationValidityStackAppend
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationValidityStackAppendTransitionProof
open InternalApplicationValidityStackAppendListProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem weakenProof {P : Formula α} {Delta : List (Formula α)}
    (h : Nonempty (Derivation body Gamma P)) (inc : ∀ p ∈ Gamma, p ∈ Delta) :
    Nonempty (Derivation body Delta P) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.weakening inc h⟩

/-- Equality is split internally by the original arithmetic comparison theorem. -/
theorem equalityCases (x y : OTerm α) (psi : Formula α)
    (kzero : ∀ Delta : List (Formula α), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 InternalEqualityTest.equalityTest z x y)) →
      Nonempty (Derivation body Delta psi))
    (kone : ∀ Delta : List (Formula α), (∀ p ∈ Gamma, p ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 InternalEqualityTest.equalityTest (suc z) x y)) →
      Nonempty (Derivation body Delta psi)) : Nonempty (Derivation body Gamma psi) := by
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Gamma)
  obtain ⟨hl⟩ := kzero (ltF x y :: Gamma) (fun p hp => List.mem_cons_of_mem _ hp)
    (InternalEqualityTestProof.rejectForwardOrder x y ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨he⟩ := kone (eqn x y :: Gamma) (fun p hp => List.mem_cons_of_mem _ hp)
    (InternalEqualityTestCompositionProof.equalityOfEqual x y ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hr⟩ := kzero (ltF y x :: Gamma) (fun p hp => List.mem_cons_of_mem _ hp)
    (InternalEqualityTestProof.rejectBackwardOrder x y ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have rest : Derivation body Gamma ((eqn x y ⊔ ltF y x).imp psi) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) rest⟩

def q0 : Program 2 := .composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 0)
def q1 : Program 2 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0)
def q2 : Program 2 := .composition append ![q1,.projection 1]
def q3 : Program 2 := leftOf q0
def q4 : Program 2 := rightOf q0
def q5 : Program 2 := leftOf q4
def q6 : Program 2 := rightOf q4
def q7 : Program 2 := leftOf q6
def q8 : Program 2 := rightOf q6
def q9 : Program 2 := leftOf q8
def q10 : Program 2 := rightOf q8
def q11 (leaf : Program 1) : Program 2 := .composition leaf (fun _ : Fin 1 => q0)
def q12 (node : Program 1) : Program 2 := .composition node (fun _ : Fin 1 => q3)
def q13 : Program 2 := consOf q7 q3
def q14 : Program 2 := pairOf q13 q9
def q15 : Program 2 := pairOf q7 q10
def q16 : Program 2 := consOf q15 q1
def q17 : Program 2 := consOf q14 q16
def q18 : Program 2 := consOf q15 q2
def q19 : Program 2 := consOf q14 q18
def q20 : Program 2 := pairOf (InternalLessThan.constantOne 2) q1
def q21 : Program 2 := pairOf (InternalLessThan.constantOne 2) q2
def q22 : Program 2 := pairOf (InternalLessThan.constantOne 2) q17
def q23 : Program 2 := pairOf (InternalLessThan.constantOne 2) q19
def queries (node leaf : Program 1) : Fin 24 → Program 2 :=
  ![q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11 leaf,q12 node,q13,q14,q15,q16,q17,q18,q19,q20,q21,q22,q23]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
