module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionOuterInductionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSingletonFoldProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectCoreNumericTargets (CountFit)
open NumberedWindowInternalCertifiedUnionStepProof (Pr unionGraph CertifiedOriginSplit)
open NumberedWindowInternalCertifiedUnionInnerProgressProof (UnionCarrierSupply)
open NumberedWindowInternalCertifiedUnionOuterInductionProof (exact_ActualOriginalConditionalJUnion)
open NumberedWindowInternalScalarSingletonInductionProof
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)

/-- The selected original list, with one actual U report per cons position.
The joined code is the literal raw constructor on that occurrence and that
exact suffix; the premise does not give J of any join. -/
def ConsUnionReports {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) : List (OTerm α) → Prop
  | [] => True
  | h :: t => Pr data c Γ (unionGraph count (singletonCode h) (packedBody t) (packedBody (h :: t))) ∧
      ConsUnionReports data c count Γ t

/-- One original positive-path certificate per original position, including
repeated terms. This does not assert an open symbolic code has been decoded. -/
def ScalarOriginReports {α : Type} (data : Data) (c : Nat)
    (Γ : List (Formula α)) (q : OTerm α) : List (OTerm α) → Prop
  | [] => True
  | h :: t => (∃ w : OTerm α, Pr data c Γ (certificate data false c q h w)) ∧
      ScalarOriginReports data c Γ q t

theorem exact_OriginalFinitePackedJ {α : Type} (data : Data) (c : Nat)
    (count : Program 2) (fit : CountFit count) (splitter : CertifiedOriginSplit data c count)
    (supply : UnionCarrierSupply data c count) (Γ : List (Formula α))
    (nilJ : Pr data c Γ (membership true (z : OTerm α))) :
    ∀ xs : List (OTerm α), ConsUnionReports data c count Γ xs →
      (∀ q ∈ xs, Pr data c Γ (singletonJ q)) →
      Pr data c Γ (membership true (packedBody xs)) := by
  intro xs
  induction xs with
  | nil =>
    intro _ _
    exact nilJ
  | cons h t ih =>
    intro reports singletons
    have headJ := singletons h List.mem_cons_self
    have tailJ := ih reports.2 (fun q hq => singletons q (List.mem_cons_of_mem _ hq))
    exact exact_ActualOriginalConditionalJUnion data c count fit splitter supply α Γ
      (singletonCode h) (packedBody t) (packedBody (h :: t)) headJ tailJ reports.1

private theorem originAt {α : Type} (data : Data) (c : Nat) (Γ : List (Formula α))
    (q : OTerm α) :
    ∀ xs : List (OTerm α), ScalarOriginReports data c Γ q xs →
      ∀ p ∈ xs, Pr data c Γ (edge data false c q p) := by
  intro xs
  induction xs with
  | nil =>
    intro _ p hm
    exact False.elim (List.not_mem_nil hm)
  | cons h t ih =>
    intro reports p hp
    rcases List.mem_cons.mp hp with rfl | tail
    · obtain ⟨w,cert⟩ := reports.1
      exact edgeIntroduction cert
    · exact ih reports.2 p tail

/-- The actual original lower-scalar hypothesis is applied to each certified
descendant and its literal singleton, then the exact recorded cons joins
yield J on the original packed target. No target J is assumed. -/
theorem exact_OriginalCertifiedScalarDescendantFold {α : Type} (data : Data) (c : Nat)
    (count : Program 2) (fit : CountFit count) (splitter : CertifiedOriginSplit data c count)
    (supply : UnionCarrierSupply data c count) (Γ : List (Formula α))
    (q : OTerm α) (xs : List (OTerm α))
    (nilJ : Pr data c Γ (membership true (z : OTerm α)))
    (lower : Pr data c Γ (scalarLower data c q))
    (origins : ScalarOriginReports data c Γ q xs)
    (joins : ConsUnionReports data c count Γ xs) :
    Pr data c Γ (membership true (packedBody xs)) := by
  apply exact_OriginalFinitePackedJ data c count fit splitter supply Γ nilJ xs joins
  intro p hp
  exact exact_ActualScalarSingletonLowerInstance data c Γ q p lower (originAt data c Γ q xs origins p hp)

#print axioms exact_OriginalFinitePackedJ
#print axioms exact_OriginalCertifiedScalarDescendantFold

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSingletonFoldProof
