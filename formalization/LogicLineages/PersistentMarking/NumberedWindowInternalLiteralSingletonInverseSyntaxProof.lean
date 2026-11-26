module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCarrierReflectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonInverseSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalSliceInduction (sliceBody)
open PositiveArithmeticPredicateSubstitution (liftPredicateFormula)
open ID1Completion.InternalSliceInductionSyntaxProof (sliceReplacement)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn eqnSubst eqnRelabel zSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst edgeSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalLiteralSingletonCarrierReflectionProof (D)

def inverse {α : Type} (m : OTerm α) : Formula α :=
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((eqn (singletonCode x) (m.relabel Sum.inl)).imp (membership false x))

def lower {α : Type} (S : Data) (c : Nat) (m : OTerm α) : Formula α :=
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((edge S true c (m.relabel Sum.inl) k).imp (inverse k))

def motive {α : Type} : Formula (α ⊕ Fin 1) := inverse (.var (.inr 0))

private theorem singleSubst {α β : Type} (x : OTerm α) (ts : α → OTerm β) :
    (singletonCode x).subst ts = singletonCode (x.subst ts) := by
  unfold singletonCode
  rw [rawConsSubst,zSubst]

theorem inverseSubst {α β : Type} (m : OTerm α) (ts : α → OTerm β) :
    (inverse m).subst (fun k => emb (ts k)) = inverse (m.subst ts) := by
  simp only [inverse,allEmbeddedSubst,impSubst,eqnSubst,singleSubst,membershipSubst,liftTermSubst]
  rfl

theorem inverseRename {α β : Type} (m : OTerm α) (j : α → β) :
    (inverse m).relabel j = inverse (m.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (inverse m).subst (fun k => emb (.var (j k))) = _
  rw [inverseSubst,← termRelabelAsSubst]

theorem lowerRename {α β : Type} (S : Data) (c : Nat) (m : OTerm α) (j : α → β) :
    (lower S c m).relabel j = lower S c (m.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (lower S c m).subst (fun k => emb (.var (j k))) = _
  simp only [lower,allEmbeddedSubst,impSubst,edgeSubst,inverseSubst,liftTermSubst,termRelabelAsSubst m j]
  rfl

theorem inverseAt {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (m x : OTerm α) (law : D B Γ (inverse m)) (e : D B Γ (eqn (singletonCode x) m)) :
    D B Γ (membership false x) := by
  obtain ⟨all⟩ := law
  obtain ⟨eq⟩ := e
  rw [inverse] at all
  have inst := Derivation.universalElimination (emb x) all
  simp only [instantiate,bindEmbedding,impSubst,eqnSubst,singleSubst,membershipSubst,liftBind,varBind] at inst
  exact ⟨Derivation.implicationElimination inst eq⟩

theorem lowerAt {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (S : Data) (c : Nat) (m n : OTerm α) (law : D B Γ (lower S c m))
    (strict : D B Γ (edge S true c m n)) : D B Γ (inverse n) := by
  obtain ⟨all⟩ := law
  obtain ⟨edge⟩ := strict
  rw [lower] at all
  have inst := Derivation.universalElimination (emb n) all
  simp only [instantiate,bindEmbedding,impSubst,edgeSubst,inverseSubst,liftBind,varBind] at inst
  exact ⟨Derivation.implicationElimination inst edge⟩

theorem edgeFromEquality {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (S : Data) (c : Nat) (m n t : OTerm α) (e : D B Γ (eqn m n))
    (h : D B Γ (edge S true c m t)) : D B Γ (edge S true c n t) := by
  let θ : Formula (α ⊕ Fin 1) := edge S true c (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl)
  have atTerm (x : OTerm α) : instantiate θ (emb x) = edge S true c x t := by
    simp only [θ,instantiate,bindEmbedding,edgeSubst,liftBind,varBind]
  obtain ⟨eq⟩ := e
  obtain ⟨edge⟩ := h
  have source : Derivation B Γ (instantiate θ (emb m)) := by rw [atTerm]; exact edge
  have res := Derivation.equalityElimination θ (emb m) (emb n) eq source
  rw [atTerm] at res
  exact ⟨res⟩

theorem exact_SingletonInverseSlice {α : Type} (S : Data) (c : Nat) :
    replacedBody (sliceBody S c true) (motive (α := α)) =
      carrier S true c (.var (.inr 0)) ⊓ lower S c (.var (.inr 0)) := by
  rw [sliceReplacement]
  simp only [motive,liftPredicateFormula,inverseRename,lower]
  rfl

theorem motiveAt {α : Type} (m : OTerm α) :
    instantiate (motive (α := α)) (emb m) = inverse m := by
  rw [motive,instantiate,bindEmbedding,inverseSubst,varBind]

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonInverseSyntaxProof
