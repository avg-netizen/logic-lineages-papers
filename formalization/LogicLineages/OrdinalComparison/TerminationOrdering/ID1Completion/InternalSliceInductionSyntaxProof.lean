module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open PositiveArithmeticPredicateSubstitution InternalCalculus SourceEndpoint TaggedArithmeticOperators
open JointGammaInvariant InternalSliceInduction SourceComputabilityFormulaSupportProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalSourceInversionSupportProof InternalSourceIntroductionSyntaxProof
open InternalTagArithmeticSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalDerivationRenamingSyntaxProof GuardedSourceSyntaxProof

def specialize (p : Positive (Fin 2)) (context : Nat) : Positive (Fin 1) :=
  substitutePositive ![numeral context,.var 0] p

def pick {α : Type} (odd : Bool) (scalar multiset : Formula (α ⊕ Fin 1)) :
    Formula (α ⊕ Fin 1) := if odd then multiset else scalar

theorem anyFormulaRelabelAsSubst {L : Language} {α β : Type}
    (phi : L.Formula α) (f : α → β) :
    phi.relabel f = phi.subst (fun a => .var (f a)) := by
  rw [formulaRelabel]
  have h := renameSubst phi f Term.var
  rw [formulaSubstVar] at h
  exact h

theorem anyFormulaSubstRelabel {L : Language} {α β γ : Type}
    (phi : L.Formula α) (ts : α → L.Term β) (f : β → γ) :
    FirstOrder.Language.Formula.relabel f (phi.subst ts) =
      phi.subst (fun a => (ts a).relabel f) := by
  rw [anyFormulaRelabelAsSubst,formulaSubstComposition]
  congr 1
  funext a
  exact (termRelabelAsSubst (ts a) f).symm

/-- Equality of the original positive syntax, before compiling to formulas. -/
theorem positiveSubstRename {α : Type} (p : Positive α) :
    ∀ (β γ : Type) (ts : α → OTerm β) (f : β → γ),
    PositiveArithmeticTransforms.relabel f (substitutePositive ts p) =
      substitutePositive (fun a => (ts a).relabel f) p := by
  induction p with
  | arithmetic phi =>
    intro β γ ts f
    exact congrArg Positive.arithmetic (anyFormulaSubstRelabel phi ts f)
  | predicate t =>
    intro β γ ts f
    exact congrArg Positive.predicate (termSubstRelabel t ts f)
  | conj p q ihp ihq =>
    intro β γ ts f
    exact congrArg₂ Positive.conj (ihp β γ ts f) (ihq β γ ts f)
  | guarded guard p ih =>
    intro β γ ts f
    exact congrArg₂ Positive.guarded (anyFormulaSubstRelabel guard ts f) (ih β γ ts f)
  | @all α p ih =>
    intro β γ ts f
    change Positive.all (PositiveArithmeticTransforms.relabel (Sum.map f id)
      (substitutePositive
        (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))) p)) = _
    rw [ih]
    congr 2
    funext a
    cases a with
    | inl a =>
      change ((ts a).relabel Sum.inl).relabel (Sum.map f id) =
        ((ts a).relabel f).relabel Sum.inl
      rw [Term.relabel_relabel,Term.relabel_relabel]
      rfl
    | inr i => rfl

theorem positiveRenameSubst {α : Type} (p : Positive α) :
    ∀ (β γ : Type) (f : α → β) (ts : β → OTerm γ),
    substitutePositive ts (PositiveArithmeticTransforms.relabel f p) =
      substitutePositive (ts ∘ f) p := by
  induction p with
  | arithmetic phi =>
    intro β γ f ts
    apply congrArg Positive.arithmetic
    rw [formulaRelabel,renameSubst]
  | predicate t =>
    intro β γ f ts
    exact congrArg Positive.predicate (termRelabelSubst t f ts)
  | conj p q ihp ihq =>
    intro β γ f ts
    exact congrArg₂ Positive.conj (ihp β γ f ts) (ihq β γ f ts)
  | guarded guard p ih =>
    intro β γ f ts
    apply congrArg₂ Positive.guarded
    · rw [formulaRelabel,renameSubst]
    · exact ih β γ f ts
  | all p ih =>
    intro β γ f ts
    change Positive.all (substitutePositive
      (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))
        (PositiveArithmeticTransforms.relabel (Sum.map f id) p)) = _
    rw [ih]
    congr 2
    funext a
    cases a <;> rfl

theorem positiveTagSubst (odd : Bool) {α : Type} (p : Positive α) :
    ∀ (β : Type) (ts : α → OTerm β),
    substitutePositive ts (tagPredicate odd p) =
      tagPredicate odd (substitutePositive ts p) := by
  induction p with
  | arithmetic phi => intro β ts; rfl
  | predicate t =>
    intro β ts
    exact congrArg Positive.predicate (tagSubstitution odd t ts)
  | conj p q ihp ihq =>
    intro β ts
    exact congrArg₂ Positive.conj (ihp β ts) (ihq β ts)
  | guarded guard p ih =>
    intro β ts
    exact congrArg (Positive.guarded (guard.subst ts)) (ih β ts)
  | all p ih =>
    intro β ts
    exact congrArg Positive.all (ih (β ⊕ Fin 1) _)

theorem specializedBody (p : Positive (Fin 2)) (context : Nat) (α : Type) :
    bodyWithParameters (specialize p context) α =
      substitutePositive ![numeral context,.var (.inr (0 : Fin 1))] p := by
  rw [bodyWithParameters,specialize,positiveSubstRename]
  congr 1
  funext i
  exact Fin.cases (numeralRename context Sum.inr)
    (Fin.cases rfl (fun j => Fin.elim0 j)) i

theorem eqnRename {α β : Type} (s t : OTerm α) (f : α → β) :
    (eqn s t).relabel f = eqn (s.relabel f) (t.relabel f) := by
  rw [eqn,InternalDerivationRenamingSyntaxProof.equalityRename,
    ← onTermRelabel,← onTermRelabel]
  rfl

theorem branchRename {α β : Type} (odd : Bool) (phi : Formula (α ⊕ Fin 1))
    (f : α → β) :
    (branch odd phi).relabel (Sum.map f id) =
      branch odd (phi.relabel (Sum.map f id)) := by
  rw [branch,onEquality,actualUniversalRenaming,branch,onEquality]
  change allOne (((eqn (.var (.inl (.inr (0 : Fin 1))))
    (tagTerm odd (.var (.inr (0 : Fin 1))))).relabel (Sum.map (Sum.map f id) id)).imp
      ((liftPredicateFormula phi).relabel (Sum.map (Sum.map f id) id))) = _
  rw [eqnRename,tagRelabel,liftRename]
  rfl

theorem liftTagged {α : Type} (scalar multiset : Formula (α ⊕ Fin 1)) :
    liftPredicateFormula (tagged scalar multiset) =
      tagged (liftPredicateFormula scalar) (liftPredicateFormula multiset) := by
  change ((branch false scalar).relabel (Sum.map Sum.inl id)) ⊓
    ((branch true multiset).relabel (Sum.map Sum.inl id)) = _
  rw [branchRename,branchRename]
  rfl

theorem liftPick {α : Type} (odd : Bool) (scalar multiset : Formula (α ⊕ Fin 1)) :
    liftPredicateFormula (pick odd scalar multiset) =
      pick odd (liftPredicateFormula scalar) (liftPredicateFormula multiset) := by
  cases odd <;> rfl

theorem replacedBodyRename (p : Positive (Fin 1)) {α β : Type}
    (theta : Formula (α ⊕ Fin 1)) (f : α → β) :
    (replacedBody p theta).relabel (Sum.map f id) =
      replacedBody p (theta.relabel (Sum.map f id)) := by
  rw [replacedBody,replacementRename,parameterBodyRename,liftRename]
  rfl

theorem replacedBodyLift (p : Positive (Fin 1)) {α : Type}
    (theta : Formula (α ⊕ Fin 1)) :
    liftPredicateFormula (replacedBody p theta) =
      replacedBody p (liftPredicateFormula theta) :=
  replacedBodyRename p theta Sum.inl

/-- Literal predicate replacement preserves the original guarded branch.
The result is the original arbitrary-formula branch, not its N-semantics. -/
theorem replacementBranch (p : Positive (Fin 2)) (context : Nat) (odd : Bool)
    {α : Type} (theta : Formula (α ⊕ Fin 1)) :
    replacedBody (specialize (taggedBranch odd p) context) theta =
      branch odd (replacedBody (specialize (tagPredicate odd p) context) theta) := by
  let guard : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    eqn (.var (.inl (.inr (0 : Fin 1)))) (tagTerm odd (.var (.inr (0 : Fin 1))))
  let value : Formula ((α ⊕ Fin 1) ⊕ Fin 1) :=
    substitutePredicate
      (substitutePositive ![numeral context,.var (.inr (0 : Fin 1))] (tagPredicate odd p))
      (liftPredicateFormula (liftPredicateFormula theta))
  calc
    replacedBody (specialize (taggedBranch odd p) context) theta =
        allOne (guard.imp value) := by
      rw [replacedBody,specializedBody]
      let sigma : Fin 2 ⊕ Fin 1 → OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
        Sum.elim
          (fun i => (![numeral context,.var (.inr (0 : Fin 1))] i : OTerm (α ⊕ Fin 1)).relabel Sum.inl)
          (fun i => .var (.inr i))
      let originalGuard : OrdinaryArithmetic.Formula (Fin 2 ⊕ Fin 1) :=
        (.var (.inl (1 : Fin 2)) : OTerm (Fin 2 ⊕ Fin 1)).equal
          (tagTerm odd (.var (.inr (0 : Fin 1))))
      change allOne ((arithmeticEmbedding.onFormula (originalGuard.subst sigma)).imp
        (substitutePredicate (substitutePositive sigma
          (PositiveArithmeticTransforms.relabel ![.inl (0 : Fin 2),.inr (0 : Fin 1)]
            (tagPredicate odd p))) (liftPredicateFormula (liftPredicateFormula theta)))) = _
      rw [positiveRenameSubst]
      have hf : sigma ∘ ![Sum.inl (0 : Fin 2),Sum.inr (0 : Fin 1)] =
          ![numeral context, (.var (.inr (0 : Fin 1)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1))] := by
        funext i
        exact Fin.cases (numeralRename context Sum.inl)
          (Fin.cases rfl (fun j => Fin.elim0 j)) i
      rw [hf]
      dsimp only [originalGuard]
      rw [equalitySubstitution,tagSubstitution,onEquality]
      rfl
    _ = branch odd (replacedBody (specialize (tagPredicate odd p) context) theta) := by
      rw [branch,onEquality,replacedBodyLift,replacedBody,specializedBody]
      rfl

theorem specializedTagBody (p : Positive (Fin 2)) (context : Nat) (odd : Bool) (α : Type) :
    bodyWithParameters (specialize (tagPredicate odd p) context) α =
      tagPredicate odd (bodyWithParameters (specialize p context) α) := by
  rw [specializedBody,specializedBody,positiveTagSubst]

theorem currentInstantiate {α : Type} (odd : Bool) (t : OTerm α) :
    instantiate (currentSlice odd) (emb t) = (Positive.predicate (tagTerm odd t)).formula := by
  rw [currentSlice,instantiate,bindEmbedding,← predicateSubstitution,tagSubstitution]
  rfl

theorem currentLift {α : Type} (odd : Bool) :
    liftPredicateFormula (currentSlice (α := α) odd) = currentSlice (α := α ⊕ Fin 1) odd := by
  rw [liftPredicateFormula,currentSlice,← predicateRename,tagRelabel]
  rfl

theorem replacementCurrent (odd : Bool) {α : Type} (p : Positive α) :
    substitutePredicate p (currentSlice odd) = (tagPredicate odd p).formula := by
  induction p with
  | arithmetic phi => rfl
  | predicate t => exact currentInstantiate odd t
  | conj p q ihp ihq => exact congrArg₂ (fun a b => a ⊓ b) ihp ihq
  | guarded guard p ih => exact congrArg (BoundedFormula.imp (arithmeticEmbedding.onFormula guard)) ih
  | all p ih =>
    change allOne (substitutePredicate p (liftPredicateFormula (currentSlice odd))) = _
    rw [currentLift,ih]
    rfl

theorem specializedCurrentReplacement (p : Positive (Fin 2)) (context : Nat) (odd : Bool)
    (α : Type) :
    replacedBody (specialize p context) (currentSlice (α := α) odd) =
      (substitutePositive ![numeral context,.var (.inr (0 : Fin 1))]
        (tagPredicate odd p)).formula := by
  rw [replacedBody,currentLift,replacementCurrent,specializedBody,positiveTagSubst]

/-- The selected closure premise is exactly the original carrier together
with all original arithmetic successors satisfying the arbitrary invariant.
This exposes the literal input needed by source-specific I/J inductions. -/
theorem sliceReplacement {α : Type} (data : SourcePresentation.Data) (context : Nat)
    (odd : Bool) (theta : Formula (α ⊕ Fin 1)) :
    replacedBody (sliceBody data context odd) theta =
      InternalAccessibilityRules.carrier data odd context (.var (.inr (0 : Fin 1))) ⊓
        allOne ((InternalAccessibilityRules.edge data odd context
          (.var (.inl (.inr (0 : Fin 1)))) (.var (.inr (0 : Fin 1)))).imp
            (liftPredicateFormula theta)) := by
  let p : Positive (Fin 2) :=
    accessibilityOperator
      (SourcePresentation.checkerFormula (InternalAccessibilityRules.carrierProgram data odd))
      (OrdinaryArithmeticQuotient.certificateGraph (InternalAccessibilityRules.edgeProgram data odd))
  have hb : sliceBody data context odd = specialize p context := by
    cases odd <;> rfl
  rw [hb,replacedBody,specializedBody]
  let sigma : Fin 2 ⊕ Fin 1 → OTerm ((α ⊕ Fin 1) ⊕ Fin 1) :=
    Sum.elim
      (fun i => (![numeral context,.var (.inr (0 : Fin 1))] i : OTerm (α ⊕ Fin 1)).relabel Sum.inl)
      (fun i => .var (.inr i))
  change InternalAccessibilityRules.carrier data odd context (.var (.inr (0 : Fin 1))) ⊓
    allOne ((arithmeticEmbedding.onFormula
      (((OrdinaryArithmeticQuotient.certificateGraph (InternalAccessibilityRules.edgeProgram data odd)).subst
        ![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))]).subst sigma)).imp
      (instantiate (liftPredicateFormula (liftPredicateFormula theta)) (.var (.inr (0 : Fin 1))))) = _
  rw [actualFreshInstantiation,formulaSubstComposition]
  have hs : (fun i : Fin 3 =>
      (![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))] i : OTerm (Fin 2 ⊕ Fin 1)).subst sigma) =
      ![numeral context,.var (.inl (.inr (0 : Fin 1))),.var (.inr (0 : Fin 1))] := by
    funext i
    exact Fin.cases (numeralRename context Sum.inl)
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rw [hs]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
