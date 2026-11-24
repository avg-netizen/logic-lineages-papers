module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitRefutationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open PositiveArithmeticOperators PositiveArithmeticOperatorsSupportProof
open SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open ID1Completion.InternalCalculusProof (actualInternalCalculusSoundness)
open ID1Completion.InternalCalculusSupportProof (actualStandardLeastModel)
open ID1Completion.InternalAccessibilityRules (edge edgeProgram)
open ID1Completion.InternalGraphComposition (graph OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.SourcePresentation (Data sourceBody)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open NumberedWindowInternalFunctionalRawUnionNumericProof (exact_FunctionalUnionOnPacked)
open NumberedWindowInternalLiteralOrderedSplitNumericProof
  (scalar relation checker witness exact_LiteralCheckerNoOrderedSplit exact_LiteralCheckerReorderedDeletion)
open ConditionalJUnionTargets (MultisetSplit splitFormula splitBody union)

def installed : Data := literalData scalar relation

private theorem unionTruth {α : Type} (P : Nat → Prop) (v : α → Nat) (a b z : OTerm α) :
    realize P (union functionalUnion a b z) v ↔
      evaluate functionalUnion (a.realize v ::ᵥ b.realize v ::ᵥ nil) = z.realize v := by
  unfold union graph
  rw [embeddingTruth,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth]
  rfl

private theorem edgeTruth {α : Type} (P : Nat → Prop) (v : α → Nat) (c : Nat) (s t : OTerm α) :
    realize P (edge installed true c s t) v ↔
      ∃ w, evaluate checker (s.realize v ::ᵥ w ::ᵥ t.realize v ::ᵥ nil) = 1 := by
  unfold edge
  rw [embeddingTruth]
  simp only [Formula.Realize,BoundedFormula.realize_subst]
  change (OrdinaryArithmeticQuotient.certificateGraph (edgeProgram installed true)).Realize
    (fun i => (![numeral c,s,t] i : OTerm α).realize v) ↔ _
  rw [OrdinaryArithmeticQuotientProof.certificateGraphTruth]
  have coordinates (w : Nat) : evaluate (edgeProgram installed true)
      (ofFn ![(numeral c : OTerm α).realize v,s.realize v,t.realize v,w]) =
      evaluate checker (s.realize v ::ᵥ w ::ᵥ t.realize v ::ᵥ nil) := by
    exact NumberedWindowCheckerCoordinatesProof.exact_ExactCoordinates.2 checker
      ((numeral c : OTerm α).realize v) (s.realize v) (t.realize v) w
  change (∃ w, evaluate (edgeProgram installed true)
      (ofFn ![(numeral c : OTerm α).realize v,s.realize v,t.realize v,w]) = 1) ↔ _
  simp only [coordinates]

private theorem equalityTruth {α : Type} (P : Nat → Prop) (v : α → Nat) (s t : OTerm α) :
    realize P (eqn s t) v ↔ s.realize v = t.realize v := by
  letI := naturalStructure P
  letI := expansion P
  unfold eqn
  simp only [realize,Formula.realize_equal,arithmeticEmbedding.realize_onTerm]

private theorem splitUntrue (c : Nat) (P : Nat → Prop) :
    ¬ realize P (splitFormula installed c functionalUnion (numeral (pack [0,0]))
      (numeral (pack [1])) (numeral (pack [1,0])) : Formula Empty) Empty.elim := by
  unfold splitFormula
  rw [existsOneTruth]
  rintro ⟨a,ha⟩
  rw [existsOneTruth] at ha
  obtain ⟨b,h⟩ := ha
  unfold splitBody at h
  rw [generalConjTruth,generalConjTruth,generalConjTruth,unionTruth,
    generalImpTruth,generalImpTruth] at h
  have left : a 0 = pack [0,0] ∨ ∃ w, evaluate checker (pack [0,0] ::ᵥ w ::ᵥ a 0 ::ᵥ nil) = 1 := by
    by_cases he : realize P (edge installed true c
      (((numeral (pack [0,0]) : OTerm Empty).relabel Sum.inl).relabel Sum.inl)
      (.var (.inl (.inr 0)))) (Sum.elim (Sum.elim Empty.elim a) b)
    · right
      rw [edgeTruth] at he
      simpa only [Term.realize_relabel,numeralTruth,Term.realize_var,Sum.elim_inl,Sum.elim_inr] using he
    · left
      have hf := h.2.1 (by exact he)
      rw [equalityTruth] at hf
      simpa only [Term.realize_relabel,numeralTruth,Term.realize_var,Sum.elim_inl,Sum.elim_inr] using hf
  have right : b 0 = pack [1] ∨ ∃ w, evaluate checker (pack [1] ::ᵥ w ::ᵥ b 0 ::ᵥ nil) = 1 := by
    by_cases he : realize P (edge installed true c
      (((numeral (pack [1]) : OTerm Empty).relabel Sum.inl).relabel Sum.inl)
      (.var (.inr 0))) (Sum.elim (Sum.elim Empty.elim a) b)
    · right
      rw [edgeTruth] at he
      simpa only [Term.realize_relabel,numeralTruth,Term.realize_var,Sum.elim_inl,Sum.elim_inr] using he
    · left
      have hf := h.2.2.1 (by exact he)
      rw [equalityTruth] at hf
      simpa only [Term.realize_relabel,numeralTruth,Term.realize_var,Sum.elim_inr] using hf
  apply exact_LiteralCheckerNoOrderedSplit (a 0) (b 0) left right
  simpa only [Term.realize_relabel,numeralTruth,Term.realize_var,Sum.elim_inl,Sum.elim_inr] using h.1

/-- The exact formula claiming an ordered split is not derivable from the
literal ordered-union and direct-edge assumptions for this installed body.
This does not refute the certified split up to permutation. -/
theorem exact_NotLiteralOrderedMultisetSplit (c : Nat) :
    ¬ MultisetSplit installed c functionalUnion := by
  intro proposed
  let m : OTerm Empty := numeral (pack [0,0])
  let n : OTerm Empty := numeral (pack [1])
  let o : OTerm Empty := numeral (pack [0,0,1])
  let t : OTerm Empty := numeral (pack [1,0])
  let u := union functionalUnion m n o
  let e := edge installed true c o t
  let Γ := [u,e]
  have split := proposed Empty Γ m n o t
    ⟨Derivation.hypothesis (by simp [Γ,u])⟩ ⟨Derivation.hypothesis (by simp [Γ,e])⟩
  let P := standardLeastPredicate (sourceBody installed c)
  apply splitUntrue c P
  apply actualInternalCalculusSoundness (sourceBody installed c) P (actualStandardLeastModel _)
    Empty Γ (splitFormula installed c functionalUnion m n t) split Empty.elim
  intro p hp
  simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · dsimp only [u,m,n,o]
    rw [unionTruth,numeralTruth,numeralTruth,numeralTruth]
    exact exact_FunctionalUnionOnPacked [0,0] [1]
  · dsimp only [e,o,t]
    rw [edgeTruth,numeralTruth,numeralTruth]
    exact ⟨witness,exact_LiteralCheckerReorderedDeletion⟩

#print axioms exact_NotLiteralOrderedMultisetSplit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitRefutationProof
