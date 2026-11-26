module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution SourceComputabilityFormulaSupportProof
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules ID1Completion.InternalSliceInduction
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding liftBind varBind zSubst zRelabel)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst membershipSubst)
open ID1Completion.InternalSliceInductionSyntaxProof (sliceReplacement)
open ID1Completion.InternalSliceInductionProof (actualInternalSliceInduction)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)

def singletonCode {α : Type} (q : OTerm α) : OTerm α := rawCons q z

def singletonJ {α : Type} (q : OTerm α) : Formula α := membership true (singletonCode q)

def scalarMotive {α : Type} : Formula (α ⊕ Fin 1) :=
  singletonJ (.var (.inr (0 : Fin 1)))

/-- The source is an even scalar, and the consequent is odd membership
of the original packed singleton of the strict scalar successor. -/
def scalarLower {α : Type} (data : Data) (c : Nat) (q : OTerm α) : Formula α :=
  allOne ((edge data false c (q.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
    (singletonJ (.var (.inr (0 : Fin 1)))))

theorem singletonSubst {α β : Type} (q : OTerm α) (ts : α → OTerm β) :
    (singletonJ q).subst (fun i => emb (ts i)) = singletonJ (q.subst ts) := by
  unfold singletonJ singletonCode
  rw [membershipSubst,rawConsSubst,zSubst]

theorem singletonRename {α β : Type} (q : OTerm α) (j : α → β) :
    (singletonJ q).relabel j = singletonJ (q.relabel j) := by
  unfold singletonJ singletonCode
  rw [membershipRename,rawConsRename,zRelabel]

theorem exact_ActualScalarSingletonLowerInstance {α : Type} (data : Data) (c : Nat)
    (Γ : List (Formula α)) (q p : OTerm α) :
    Nonempty (Derivation (sourceBody data c) Γ (scalarLower data c q)) →
    Nonempty (Derivation (sourceBody data c) Γ (edge data false c q p)) →
    Nonempty (Derivation (sourceBody data c) Γ (singletonJ p)) := by
  rintro ⟨lower⟩ ⟨strict⟩
  have h := Derivation.universalElimination (emb p) lower
  simp only [instantiate,bindEmbedding,impSubst,edgeSubst,singletonSubst,liftBind,varBind] at h
  exact ⟨Derivation.implicationElimination h strict⟩

/-- Open progress for the precise manuscript singleton step, before any
certificate reconstruction or finite union of the successor occurrences. -/
def ActualScalarSingletonProgressiveInduction : Prop :=
  ∀ (data : Data) (c : Nat) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    Nonempty (Derivation (sourceBody data c)
      (carrier data false c x :: scalarLower data c x :: Γ.map weaken) (singletonJ x)) →
    Nonempty (Derivation (sourceBody data c) Γ ((membership false q).imp (singletonJ q)))

theorem exact_ActualScalarSingletonProgressiveInduction :
    ActualScalarSingletonProgressiveInduction := by
  intro data c α Γ q
  dsimp only
  rintro ⟨progress⟩
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let C := carrier data false c x
  let L := scalarLower data c x
  let original := replacedBody (sliceBody data c false) (scalarMotive (α := α))
  let Δ := original :: Γ.map weaken
  have hl : liftPredicateFormula (scalarMotive (α := α)) =
      singletonJ (.var (.inr (0 : Fin 1))) := by
    rw [liftPredicateFormula,scalarMotive,singletonRename] <;> rfl
  have originalEq : original = C ⊓ L := by
    dsimp only [original,C,L]
    rw [sliceReplacement,hl] <;> rfl
  have openClosure : Nonempty (Derivation (sourceBody data c) Δ (scalarMotive (α := α))) := by
    have h : Derivation (sourceBody data c) Δ original :=
      Derivation.hypothesis List.mem_cons_self
    have pair : Derivation (sourceBody data c) Δ (C ⊓ L) :=
      Eq.mp (congrArg (Derivation (sourceBody data c) Δ) originalEq) h
    have consequence : Derivation (sourceBody data c) (Γ.map weaken) (L.imp (C.imp (singletonJ x))) :=
      Derivation.implicationIntroduction (Derivation.implicationIntroduction progress)
    have moved : Derivation (sourceBody data c) Δ (L.imp (C.imp (singletonJ x))) :=
      Derivation.weakening (fun _ hz => List.mem_cons_of_mem _ hz) consequence
    exact ⟨Derivation.implicationElimination
      (Derivation.implicationElimination moved (Derivation.conjunctionRight pair))
      (Derivation.conjunctionLeft pair)⟩
  have h := actualInternalSliceInduction data c α Γ false scalarMotive q openClosure
  have atQ : instantiate (scalarMotive (α := α)) (emb q) = singletonJ q := by
    rw [scalarMotive,instantiate,bindEmbedding,singletonSubst,varBind]
  rw [atQ] at h
  exact h

#print axioms exact_ActualScalarSingletonLowerInstance
#print axioms exact_ActualScalarSingletonProgressiveInduction

end LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof
