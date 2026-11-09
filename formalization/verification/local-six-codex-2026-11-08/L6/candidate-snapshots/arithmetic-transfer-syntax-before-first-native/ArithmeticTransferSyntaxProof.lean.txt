module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof

@[expose] public section
/-! Literal substitution and binder bookkeeping for the arithmetic proof
transfer. This module proves syntax equalities only, on the frozen translator. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Syntax
open GorbowSyntax
open LogicLineages.OrdinalComparison.TerminationOrdering
local notation "ABF" => PositiveArithmeticOperators.language.BoundedFormula

private theorem trSubst {α : Type} {m n : Nat} (τ : Fin m → Term n) (ρ : α → Term m)
    (t : SourceTerm α) :
    GorbowSubstitution.substitute τ (translateTerm ρ t) =
      translateTerm (fun a => GorbowSubstitution.substitute τ (ρ a)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem trRelabel {α β : Type} {m : Nat} (ρ : β → Term m) (g : α → β)
    (t : SourceTerm α) :
    translateTerm ρ (FirstOrder.Language.Term.relabel g t) = translateTerm (fun a => ρ (g a)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem trMSubst {α β : Type} {m : Nat} (ρ : β → Term m)
    (s : α → SourceTerm β) (t : SourceTerm α) :
    translateTerm ρ (FirstOrder.Language.Term.subst t s) = translateTerm (fun x => translateTerm ρ (s x)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem renameTr {α : Type} {m : Nat} (t : SourceTerm α) (ρ : α → Term m) :
    translateTerm (fun a => GorbowFormulaSubstitution.renameTerm Fin.succ (ρ a)) t =
      GorbowFormulaSubstitution.renameTerm Fin.succ (translateTerm ρ t) :=
  (trSubst (fun i => Term.var (Fin.succ i)) ρ t).symm

/-! ### Binder bookkeeping -/

private theorem shiftSubst {m n : Nat} (τ : Fin m → Term n) (t : Term m) :
    GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute τ)
      (GorbowFormulaSubstitution.renameTerm Fin.succ t) =
      GorbowFormulaSubstitution.renameTerm Fin.succ (GorbowSubstitution.substitute τ t) := by
  simp only [GorbowFormulaSubstitution.renameTerm, GorbowSubstitution.substitute_composition,
    GorbowSubstitution.substitute, GorbowFormulaSubstitution.liftSubstitute, Fin.cases_succ]

private theorem cancelShift {n : Nat} (t : Term n) (x : Term n) :
    GorbowSubstitution.substitute (Fin.cases t Term.var : Fin (n+1) → Term n)
      (GorbowFormulaSubstitution.renameTerm Fin.succ x) = x := by
  unfold GorbowFormulaSubstitution.renameTerm
  rw [GorbowSubstitution.substitute_composition]
  exact GorbowSubstitution.substitute_variables x

private theorem lastVar {l m : Nat} (bound : Fin l → Fin m) :
    (fun i => Term.var ((Fin.lastCases (0 : Fin (m+1)) (fun i => (bound i).succ) :
      Fin (l+1) → Fin (m+1)) i)) =
      (Fin.lastCases (Term.var 0) (fun i => GorbowFormulaSubstitution.renameTerm Fin.succ
        (Term.var (bound i))) : Fin (l+1) → Term (m+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
  · simp only [Fin.lastCases_castSucc, GorbowFormulaSubstitution.renameTerm,
      GorbowSubstitution.substitute]

private theorem liftLast {l m n : Nat} (τ : Fin m → Term n) (β : Fin l → Term m) :
    (fun i => GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute τ)
      ((Fin.lastCases (Term.var 0) (fun j => GorbowFormulaSubstitution.renameTerm Fin.succ (β j)) :
        Fin (l+1) → Term (m+1)) i)) =
    (Fin.lastCases (Term.var 0) (fun j => GorbowFormulaSubstitution.renameTerm Fin.succ
      (GorbowSubstitution.substitute τ (β j))) : Fin (l+1) → Term (n+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]; rfl
  · simp only [Fin.lastCases_castSucc]; exact shiftSubst τ (β j)

private theorem snocShift {l : Nat} (β : Fin l → Term 0) (t : Term 0) :
    (fun i => GorbowSubstitution.substitute (Fin.cases t Term.var : Fin 1 → Term 0)
      ((Fin.lastCases (Term.var 0) (fun j => GorbowFormulaSubstitution.renameTerm Fin.succ (β j)) :
        Fin (l+1) → Term 1) i)) = Fin.snoc β t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, Fin.snoc_last]; rfl
  · simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc]; exact cancelShift t (β j)

private theorem castAddSucc {n k : Nat} (j : Fin n) :
    (Fin.castAdd (k+1) j : Fin (n + (k+1))) = (Fin.castSucc (Fin.castAdd k j) : Fin (n + k + 1)) :=
  Fin.ext rfl

private theorem natAddLast {n k : Nat} :
    (Fin.natAdd n (Fin.last k) : Fin (n + (k+1))) = (Fin.last (n + k) : Fin (n + k + 1)) :=
  Fin.ext rfl

private theorem natAddCastSucc {n k : Nat} (i : Fin k) :
    (Fin.natAdd n (Fin.castSucc i) : Fin (n + (k+1))) =
      (Fin.castSucc (Fin.natAdd n i) : Fin (n + k + 1)) :=
  Fin.ext rfl

private theorem substTr {α : Type} {l : Nat} (φ : ABF α l) :
    ∀ {m n : Nat} (τ : Fin m → Term n) (ρ : α → Term m) (β : Fin l → Term m),
      GorbowFormulaSubstitution.substituteFormula τ (translateBounded φ ρ β) =
        translateBounded φ (fun a => GorbowSubstitution.substitute τ (ρ a))
          (fun i => GorbowSubstitution.substitute τ (β i)) := by
  induction φ with
  | falsum => intro m n τ ρ β; rfl
  | equal t u =>
    intro m n τ ρ β
    have he : (fun x => GorbowSubstitution.substitute τ (Sum.elim ρ β x)) =
        Sum.elim (fun a => GorbowSubstitution.substitute τ (ρ a))
          (fun i => GorbowSubstitution.substitute τ (β i)) := by
      funext x; cases x <;> rfl
    exact congrArg₂ Formula.equal
      ((trSubst τ _ t).trans (congrArg (fun r => translateTerm r t) he))
      ((trSubst τ _ u).trans (congrArg (fun r => translateTerm r u) he))
  | rel _ _ => intro m n tau rho beta; rfl
  | imp a b iha ihb =>
    intro m n τ ρ β
    exact congrArg₂ Formula.imp (iha τ ρ β) (ihb τ ρ β)
  | all a ih =>
    intro m n τ ρ β
    refine congrArg Formula.all ((ih _ _ _).trans ?_)
    exact congrArg₂ (translateBounded a) (funext fun x => shiftSubst τ (ρ x)) (liftLast τ β)

private theorem auxAgree {α β : Type} {n k m : Nat} (g : α → β ⊕ Fin n) (ρ : β → Term m)
    (bs : Fin (n + k) → Term m) :
    (fun x => Sum.elim ρ bs (FirstOrder.Language.BoundedFormula.relabelAux g k x)) =
      Sum.elim (fun a => Sum.elim ρ (fun i => bs (Fin.castAdd k i)) (g a))
        (fun i => bs (Fin.natAdd n i)) :=
  FirstOrder.Language.BoundedFormula.sumElim_comp_relabelAux

private theorem relabelTr {α β : Type} {n : Nat} (g : α → β ⊕ Fin n) {k : Nat} (φ : ABF α k) :
    ∀ {m : Nat} (ρ : β → Term m) (bs : Fin (n + k) → Term m),
      translateBounded (FirstOrder.Language.BoundedFormula.relabel g φ) ρ bs =
        translateBounded φ (fun a => Sum.elim ρ (fun i => bs (Fin.castAdd k i)) (g a))
          (fun i => bs (Fin.natAdd n i)) := by
  induction φ with
  | falsum => intro m ρ bs; rfl
  | equal t u =>
    intro m ρ bs
    exact congrArg₂ Formula.equal
      ((trRelabel _ _ t).trans (congrArg (fun r => translateTerm r t) (auxAgree g ρ bs)))
      ((trRelabel _ _ u).trans (congrArg (fun r => translateTerm r u) (auxAgree g ρ bs)))
  | rel _ _ => intro m rho bs; rfl
  | imp a b iha ihb =>
    intro m ρ bs
    exact congrArg₂ Formula.imp (iha ρ bs) (ihb ρ bs)
  | all a ih =>
    intro m ρ bs
    rw [FirstOrder.Language.BoundedFormula.relabel_all]
    refine congrArg Formula.all ((ih _ _).trans
      (congrArg₂ (translateBounded a) (funext fun x => ?_) (funext fun i => ?_)))
    · cases h : g x with
      | inl b => simp only [h, Sum.elim_inl]
      | inr j =>
        simp only [h, Sum.elim_inr]
        rw [castAddSucc, Fin.lastCases_castSucc]
    · refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [natAddLast, Fin.lastCases_last, Fin.lastCases_last]
      · rw [natAddCastSucc, Fin.lastCases_castSucc, Fin.lastCases_castSucc]

private theorem substAgree {α γ : Type} {l m : Nat} (tf : α → SourceTerm γ)
    (ρ : γ → Term m) (bs : Fin l → Term m) :
    (fun x => translateTerm (Sum.elim ρ bs)
      (Sum.elim (FirstOrder.Language.Term.relabel Sum.inl ∘ tf)
        (FirstOrder.Language.Term.var ∘ Sum.inr) x)) =
      Sum.elim (fun a => translateTerm ρ (tf a)) bs := by
  funext x
  cases x with
  | inl a => exact trRelabel (Sum.elim ρ bs) Sum.inl (tf a)
  | inr i => rfl

private theorem substBoundedTr {α γ : Type} {l : Nat} (φ : ABF α l)
    (tf : α → SourceTerm γ) :
    ∀ {m : Nat} (ρ : γ → Term m) (bs : Fin l → Term m),
      translateBounded (FirstOrder.Language.BoundedFormula.subst φ tf) ρ bs = translateBounded φ (fun a => translateTerm ρ (tf a)) bs := by
  induction φ with
  | falsum => intro m ρ bs; rfl
  | equal t u =>
    intro m ρ bs
    exact congrArg₂ Formula.equal
      ((trMSubst _ _ t).trans (congrArg (fun r => translateTerm r t) (substAgree tf ρ bs)))
      ((trMSubst _ _ u).trans (congrArg (fun r => translateTerm r u) (substAgree tf ρ bs)))
  | rel _ _ => intro m rho bs; rfl
  | imp a b iha ihb =>
    intro m ρ bs
    exact congrArg₂ Formula.imp (iha ρ bs) (ihb ρ bs)
  | all a ih =>
    intro m ρ bs
    refine congrArg Formula.all ((ih _ _).trans ?_)
    exact congrArg (fun r => translateBounded a r _) (funext fun x => renameTr (tf x) ρ)


theorem translateGorbowSubstitution {alpha : Type} {m n : Nat}
    (phi : SourceFormula alpha) (rho : alpha → Term m) (tau : Fin m → Term n) :
    GorbowFormulaSubstitution.substituteFormula tau (translate phi rho) =
      translate phi (fun a => GorbowSubstitution.substitute tau (rho a)) := by
  unfold translate
  exact (substTr phi tau rho Fin.elim0).trans
    (congrArg (translateBounded phi _) (funext fun i => Fin.elim0 i))

theorem translateSourceSubstitution {alpha beta : Type} {m : Nat}
    (phi : SourceFormula alpha) (tf : alpha → SourceTerm beta) (rho : beta → Term m) :
    translate (phi.subst tf) rho = translate phi (fun a => translateTerm rho (tf a)) :=
  substBoundedTr phi tf rho Fin.elim0

theorem translateRelabel {alpha beta : Type} {m : Nat}
    (phi : SourceFormula alpha) (g : alpha → beta) (rho : beta → Term m) :
    translate (phi.relabel g) rho = translate phi (fun a => rho (g a)) := by
  unfold FirstOrder.Language.Formula.relabel translate
  exact (relabelTr (Sum.inl ∘ g) phi rho Fin.elim0).trans
    (congrArg (translateBounded phi _) (funext fun i => Fin.elim0 i))

def liftMap {alpha : Type} {m : Nat} (rho : alpha → Term m) : alpha ⊕ Fin 1 → Term (m+1) :=
  Sum.elim (fun a => GorbowFormulaSubstitution.renameTerm Fin.succ (rho a)) (fun _ => .var 0)

theorem translateAllOne {alpha : Type} {m : Nat}
    (phi : SourceFormula (alpha ⊕ Fin 1)) (rho : alpha → Term m) :
    translate (SourceComputabilityFormulaSupportProof.allOne phi) rho =
      Formula.all (translate phi (liftMap rho)) := by
  unfold SourceComputabilityFormulaSupportProof.allOne translate
  change Formula.all (translateBounded (FirstOrder.Language.BoundedFormula.relabel id phi)
    (fun a => GorbowFormulaSubstitution.renameTerm Fin.succ (rho a))
    (Fin.lastCases (.var 0) (fun i : Fin 0 => Fin.elim0 i))) = _
  apply congrArg Formula.all
  refine (relabelTr id phi _ _).trans ?_
  apply congrArg₂ (translateBounded phi)
  · funext a
    cases a with
    | inl a => rfl
    | inr i =>
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
  · exact funext fun i => Fin.elim0 i

theorem translateEquality {alpha : Type} {m : Nat}
    (t u : SourceTerm alpha) (rho : alpha → Term m) :
    translate (t.equal u) rho = Formula.equal (translateTerm rho t) (translateTerm rho u) := by
  unfold FirstOrder.Language.Term.equal FirstOrder.Language.Term.bdEqual translate
  change Formula.equal
    (translateTerm (Sum.elim rho Fin.elim0) (t.relabel Sum.inl))
    (translateTerm (Sum.elim rho Fin.elim0) (u.relabel Sum.inl)) = _
  rw [trRelabel,trRelabel]
  rfl

theorem translateWeaken {alpha : Type} {m : Nat}
    (phi : SourceFormula alpha) (rho : alpha → Term m) :
    translate (ID1Completion.InternalCalculus.weaken phi) (liftMap rho) =
      GorbowPACore.weaken (translate phi rho) := by
  rw [ID1Completion.InternalCalculus.weaken,translateRelabel]
  exact (translateGorbowSubstitution phi rho (fun i => Term.var i.succ)).symm

theorem translateInstantiate {alpha : Type} {m : Nat}
    (phi : SourceFormula (alpha ⊕ Fin 1)) (t : SourceTerm alpha) (rho : alpha → Term m) :
    translate (ID1Completion.InternalCalculus.instantiate phi t) rho =
      GorbowStandardInstances.instantiate (translate phi (liftMap rho)) (translateTerm rho t) := by
  rw [ID1Completion.InternalCalculus.instantiate,translateSourceSubstitution]
  rw [GorbowStandardInstances.instantiate,translateGorbowSubstitution]
  apply congrArg (translate phi)
  funext a
  cases a with
  | inl a =>
      change rho a = GorbowSubstitution.substitute (Fin.cases (translateTerm rho t) Term.var)
        (GorbowFormulaSubstitution.renameTerm Fin.succ (rho a))
      exact (cancelShift (translateTerm rho t) (rho a)).symm
  | inr i => rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Syntax
