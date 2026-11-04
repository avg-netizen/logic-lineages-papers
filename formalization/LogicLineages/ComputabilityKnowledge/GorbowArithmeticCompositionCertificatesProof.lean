module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificatesTargets
public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsProof

@[expose] public section
/-! Internal Hilbert certificates for the recursion-free fragment of the actual
Program AST, through the exact ordinary-arithmetic compiler and its literal
Gorbow translation. A term-valued generalization of the translator commutes
with Gorbow substitution, Mathlib relabelling and Mathlib substitution; the
encoded existential and conjunction are derived with actual K/S/all-instance
axioms and modus ponens. No semantic inference, graph-correctness axiom,
primitive recursion, totality, uniqueness or internal HB is involved. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

local notation "ABF" => OrdinaryArithmetic.arithmeticLanguage.BoundedFormula

/-! ### Actual Hilbert combinators -/

private def idProof (A : Sentence → Prop) {n : Nat} (a : Formula n) : Derivation A (.imp a a) :=
  .mp (.mp (.logical (.s a (.imp a a) a)) (.logical (.k a (.imp a a)))) (.logical (.k a a))

private def liftP {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) :=
  .mp (.logical (.k a r)) p

private def sApp {A : Sentence → Prop} {n : Nat} {x y z : Formula n}
    (p : Derivation A (.imp x (.imp y z))) (q : Derivation A (.imp x y)) : Derivation A (.imp x z) :=
  .mp (.mp (.logical (.s x y z)) p) q

private def pairProof {A : Sentence → Prop} {x y : Sentence} (px : Derivation A x)
    (py : Derivation A y) :
    Derivation A (.imp (.imp x (.imp y falseFormula)) falseFormula) :=
  sApp (sApp (idProof A (.imp x (.imp y falseFormula))) (liftP _ px)) (liftP _ py)

private def witnessProof {A : Sentence → Prop} (a : Formula 1) (t : Term 0)
    (p : Derivation A (GorbowStandardInstances.instantiate a t)) : Derivation A (encodedExists a) :=
  sApp (x := .all (.imp a falseFormula)) (y := GorbowStandardInstances.instantiate a t)
    (z := falseFormula) (.logical (.allInstantiate (.imp a falseFormula) t)) (liftP _ p)

theorem witnessIntroduction : GorbowArithmeticCompositionCertificates.Targets.WitnessIntroduction := by
  intro T a t h
  obtain ⟨d⟩ := h
  exact ⟨witnessProof a t d⟩

/-! ### Term-valued translation -/

private def trT {α : Type} {m : Nat} (ρ : α → Term m) : OrdinaryArithmetic.Term α → Term m
  | .var i => ρ i
  | .func .zero _ => .zero
  | .func .succ ts => .succ (trT ρ (ts 0))
  | .func .add ts => .add (trT ρ (ts 0)) (trT ρ (ts 1))
  | .func .mul ts => .mul (trT ρ (ts 0)) (trT ρ (ts 1))

private def trB {α : Type} : {l m : Nat} → ABF α l → (α → Term m) → (Fin l → Term m) → Formula m
  | _, _, .falsum, _, _ => .neg (.equal .zero .zero)
  | _, _, .equal t u, ρ, β => .equal (trT (Sum.elim ρ β) t) (trT (Sum.elim ρ β) u)
  | _, _, .rel r _, _, _ => nomatch r
  | _, _, .imp a b, ρ, β => .imp (trB a ρ β) (trB b ρ β)
  | _, _, .all a, ρ, β => .all (trB a (fun i => GorbowFormulaSubstitution.renameTerm Fin.succ (ρ i))
      (Fin.lastCases (.var 0) (fun i => GorbowFormulaSubstitution.renameTerm Fin.succ (β i))))

private theorem translateAsTr {α : Type} {m : Nat} (r : α → Fin m) (t : OrdinaryArithmetic.Term α) :
    GorbowOrdinaryArithmeticGraphs.translateTerm r t = trT (fun a => Term.var (r a)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem trSubst {α : Type} {m n : Nat} (τ : Fin m → Term n) (ρ : α → Term m)
    (t : OrdinaryArithmetic.Term α) :
    GorbowSubstitution.substitute τ (trT ρ t) =
      trT (fun a => GorbowSubstitution.substitute τ (ρ a)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem trRelabel {α β : Type} {m : Nat} (ρ : β → Term m) (g : α → β)
    (t : OrdinaryArithmetic.Term α) :
    trT ρ (FirstOrder.Language.Term.relabel g t) = trT (fun a => ρ (g a)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem trMSubst {α β : Type} {m : Nat} (ρ : β → Term m)
    (s : α → OrdinaryArithmetic.Term β) (t : OrdinaryArithmetic.Term α) :
    trT ρ (FirstOrder.Language.Term.subst t s) = trT (fun x => trT ρ (s x)) t := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Term.succ (ih 0)
    | add => exact congrArg₂ Term.add (ih 0) (ih 1)
    | mul => exact congrArg₂ Term.mul (ih 0) (ih 1)

private theorem renameTr {α : Type} {m : Nat} (t : OrdinaryArithmetic.Term α) (ρ : α → Term m) :
    trT (fun a => GorbowFormulaSubstitution.renameTerm Fin.succ (ρ a)) t =
      GorbowFormulaSubstitution.renameTerm Fin.succ (trT ρ t) :=
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

/-! ### Commutation of the translations -/

private theorem boundedAsTr {α : Type} {l : Nat} (φ : ABF α l) :
    ∀ {m : Nat} (free : α → Fin m) (bound : Fin l → Fin m),
      GorbowOrdinaryArithmeticGraphs.translateBounded φ free bound =
        trB φ (fun a => Term.var (free a)) (fun i => Term.var (bound i)) := by
  induction φ with
  | falsum => intro m free bound; rfl
  | equal t u =>
    intro m free bound
    have he : (fun x => Term.var (Sum.elim free bound x)) =
        Sum.elim (fun a => Term.var (free a)) (fun i => Term.var (bound i)) := by
      funext x; cases x <;> rfl
    exact congrArg₂ Formula.equal
      ((translateAsTr (Sum.elim free bound) t).trans (congrArg (fun r => trT r t) he))
      ((translateAsTr (Sum.elim free bound) u).trans (congrArg (fun r => trT r u) he))
  | rel r _ => exact Empty.elim r
  | imp a b iha ihb =>
    intro m free bound
    exact congrArg₂ Formula.imp (iha free bound) (ihb free bound)
  | all a ih =>
    intro m free bound
    exact congrArg Formula.all
      ((ih (fun i => (free i).succ) (Fin.lastCases 0 (fun i => (bound i).succ))).trans
        (congrArg (fun β => trB a (fun x => Term.var ((free x).succ)) β) (lastVar bound)))

private theorem substTr {α : Type} {l : Nat} (φ : ABF α l) :
    ∀ {m n : Nat} (τ : Fin m → Term n) (ρ : α → Term m) (β : Fin l → Term m),
      GorbowFormulaSubstitution.substituteFormula τ (trB φ ρ β) =
        trB φ (fun a => GorbowSubstitution.substitute τ (ρ a))
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
      ((trSubst τ _ t).trans (congrArg (fun r => trT r t) he))
      ((trSubst τ _ u).trans (congrArg (fun r => trT r u) he))
  | rel r _ => exact Empty.elim r
  | imp a b iha ihb =>
    intro m n τ ρ β
    exact congrArg₂ Formula.imp (iha τ ρ β) (ihb τ ρ β)
  | all a ih =>
    intro m n τ ρ β
    refine congrArg Formula.all ((ih _ _ _).trans ?_)
    exact congrArg₂ (trB a) (funext fun x => shiftSubst τ (ρ x)) (liftLast τ β)

private theorem substTranslate {α : Type} {l m n : Nat} (φ : ABF α l) (σ : Fin m → Term n)
    (free : α → Fin m) (bound : Fin l → Fin m) :
    GorbowFormulaSubstitution.substituteFormula σ
        (GorbowOrdinaryArithmeticGraphs.translateBounded φ free bound) =
      trB φ (fun a => σ (free a)) (fun i => σ (bound i)) := by
  rw [boundedAsTr φ free bound]
  exact substTr φ σ _ _

private theorem auxAgree {α β : Type} {n k m : Nat} (g : α → β ⊕ Fin n) (ρ : β → Term m)
    (bs : Fin (n + k) → Term m) :
    (fun x => Sum.elim ρ bs (FirstOrder.Language.BoundedFormula.relabelAux g k x)) =
      Sum.elim (fun a => Sum.elim ρ (fun i => bs (Fin.castAdd k i)) (g a))
        (fun i => bs (Fin.natAdd n i)) :=
  FirstOrder.Language.BoundedFormula.sumElim_comp_relabelAux

private theorem relabelTr {α β : Type} {n : Nat} (g : α → β ⊕ Fin n) {k : Nat} (φ : ABF α k) :
    ∀ {m : Nat} (ρ : β → Term m) (bs : Fin (n + k) → Term m),
      trB (FirstOrder.Language.BoundedFormula.relabel g φ) ρ bs =
        trB φ (fun a => Sum.elim ρ (fun i => bs (Fin.castAdd k i)) (g a))
          (fun i => bs (Fin.natAdd n i)) := by
  induction φ with
  | falsum => intro m ρ bs; rfl
  | equal t u =>
    intro m ρ bs
    exact congrArg₂ Formula.equal
      ((trRelabel _ _ t).trans (congrArg (fun r => trT r t) (auxAgree g ρ bs)))
      ((trRelabel _ _ u).trans (congrArg (fun r => trT r u) (auxAgree g ρ bs)))
  | rel r _ => exact Empty.elim r
  | imp a b iha ihb =>
    intro m ρ bs
    exact congrArg₂ Formula.imp (iha ρ bs) (ihb ρ bs)
  | all a ih =>
    intro m ρ bs
    rw [FirstOrder.Language.BoundedFormula.relabel_all]
    refine congrArg Formula.all ((ih _ _).trans
      (congrArg₂ (trB a) (funext fun x => ?_) (funext fun i => ?_)))
    · cases h : g x with
      | inl b => simp only [h, Sum.elim_inl]
      | inr j =>
        simp only [h, Sum.elim_inr]
        rw [castAddSucc, Fin.lastCases_castSucc]
    · refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [natAddLast, Fin.lastCases_last, Fin.lastCases_last]
      · rw [natAddCastSucc, Fin.lastCases_castSucc, Fin.lastCases_castSucc]

private theorem substAgree {α γ : Type} {l m : Nat} (tf : α → OrdinaryArithmetic.Term γ)
    (ρ : γ → Term m) (bs : Fin l → Term m) :
    (fun x => trT (Sum.elim ρ bs)
      (Sum.elim (FirstOrder.Language.Term.relabel Sum.inl ∘ tf)
        (FirstOrder.Language.Term.var ∘ Sum.inr) x)) =
      Sum.elim (fun a => trT ρ (tf a)) bs := by
  funext x
  cases x with
  | inl a => exact trRelabel (Sum.elim ρ bs) Sum.inl (tf a)
  | inr i => rfl

private theorem substBoundedTr {α γ : Type} {l : Nat} (φ : ABF α l)
    (tf : α → OrdinaryArithmetic.Term γ) :
    ∀ {m : Nat} (ρ : γ → Term m) (bs : Fin l → Term m),
      trB (FirstOrder.Language.BoundedFormula.subst φ tf) ρ bs = trB φ (fun a => trT ρ (tf a)) bs := by
  induction φ with
  | falsum => intro m ρ bs; rfl
  | equal t u =>
    intro m ρ bs
    exact congrArg₂ Formula.equal
      ((trMSubst _ _ t).trans (congrArg (fun r => trT r t) (substAgree tf ρ bs)))
      ((trMSubst _ _ u).trans (congrArg (fun r => trT r u) (substAgree tf ρ bs)))
  | rel r _ => exact Empty.elim r
  | imp a b iha ihb =>
    intro m ρ bs
    exact congrArg₂ Formula.imp (iha ρ bs) (ihb ρ bs)
  | all a ih =>
    intro m ρ bs
    refine congrArg Formula.all ((ih _ _).trans ?_)
    exact congrArg (fun r => trB a r _) (funext fun x => renameTr (tf x) ρ)

/-! ### Witness blocks -/

private theorem instantiateShift {α : Type} {l : Nat} (φ : ABF α (l+1)) (ρ : α → Term 0)
    (β : Fin l → Term 0) (t : Term 0) :
    GorbowStandardInstances.instantiate
      (trB φ (fun a => GorbowFormulaSubstitution.renameTerm Fin.succ (ρ a))
        (Fin.lastCases (Term.var 0) (fun i => GorbowFormulaSubstitution.renameTerm Fin.succ (β i)) :
          Fin (l+1) → Term 1)) t =
      trB φ ρ (Fin.snoc β t) := by
  unfold GorbowStandardInstances.instantiate
  rw [substTr]
  exact congrArg₂ (trB φ) (funext fun a => cancelShift t (ρ a)) (snocShift β t)

private theorem exStep {T : Sentence → Prop} {α : Type} {l : Nat} (φ : ABF α (l+1))
    (ρ : α → Term 0) (β : Fin l → Term 0) (t : Term 0)
    (h : Nonempty (Derivation T (trB φ ρ (Fin.snoc β t)))) :
    Nonempty (Derivation T (trB φ.ex ρ β)) := by
  obtain ⟨d⟩ := h
  exact ⟨witnessProof _ t
    (cast (congrArg (fun x : Sentence => Derivation T x) (instantiateShift φ ρ β t).symm) d)⟩

private theorem exsIntro {T : Sentence → Prop} {α : Type} (ρ : α → Term 0) :
    ∀ (j : Nat) (φ : ABF α j) (β : Fin j → Term 0),
      Nonempty (Derivation T (trB φ ρ β)) → Nonempty (Derivation T (trB φ.exs ρ Fin.elim0))
  | 0, φ, β, h => by
    have hb : β = Fin.elim0 := funext fun i => Fin.elim0 i
    subst hb
    exact h
  | j+1, φ, β, h => by
    have h' : Nonempty (Derivation T (trB φ ρ (Fin.snoc (Fin.init β) (β (Fin.last j))))) := by
      rw [Fin.snoc_init_self]; exact h
    exact exsIntro ρ j φ.ex (Fin.init β) (exStep φ ρ (Fin.init β) (β (Fin.last j)) h')

/-! ### Finite conjunctions -/

private theorem andFinTr {T : Sentence → Prop} {α : Type} (ρ : α → Term 0) :
    ∀ (k : Nat) (p : Fin k → OrdinaryArithmetic.Formula α) (bs : Fin 0 → Term 0),
      (∀ i, Nonempty (Derivation T (trB (p i) ρ bs))) →
        Nonempty (Derivation T (trB (OrdinaryArithmetic.andFin p) ρ bs))
  | 0, p, bs, _ => by
    have e : OrdinaryArithmetic.andFin p = (⊤ : OrdinaryArithmetic.Formula α) := by
      simp only [OrdinaryArithmetic.andFin, List.ofFn_zero, List.foldr_nil]
    rw [e]
    exact ⟨idProof T falseFormula⟩
  | k+1, p, bs, h => by
    have e : OrdinaryArithmetic.andFin p = p 0 ⊓ OrdinaryArithmetic.andFin (fun i => p i.succ) := by
      simp only [OrdinaryArithmetic.andFin, List.ofFn_succ, List.foldr_cons]
    rw [e]
    obtain ⟨d0⟩ := h 0
    obtain ⟨dr⟩ := andFinTr ρ k (fun i => p i.succ) bs (fun i => h i.succ)
    exact ⟨pairProof d0 dr⟩

private theorem closedArithmeticTr {n : Nat} (a : OrdinaryArithmetic.Formula (Fin n)) (v : Fin n → Nat) :
    closedArithmetic a v = trB a (fun j => Term.numeral (v j)) Fin.elim0 :=
  (substTranslate a (fun j => Term.numeral (v j)) id Fin.elim0).trans
    (congrArg (trB a (fun j => Term.numeral (v j))) (funext fun i => Fin.elim0 i))

theorem finiteConjunction : GorbowArithmeticCompositionCertificates.Targets.FiniteConjunction := by
  intro T k n a v h
  rw [closedArithmeticTr]
  exact andFinTr (fun j => Term.numeral (v j)) k a Fin.elim0
    (fun i => (congrArg (fun x : Sentence => Nonempty (Derivation T x))
      (closedArithmeticTr (a i) v)).mp (h i))

/-! ### Composition -/

private theorem closedGraphTr {n : Nat} (p : Program n) (inputs : List.Vector Nat n) (out : Nat) :
    GorbowOrdinaryArithmeticGraphs.closedGraph p inputs out =
      trB (OrdinaryArithmetic.graphFormula p)
        (Fin.cases (Term.numeral out) (fun i => Term.numeral (inputs.get i)) : Fin (n+1) → Term 0)
        Fin.elim0 :=
  (substTranslate _ _ id Fin.elim0).trans (congrArg (trB _ _) (funext fun i => Fin.elim0 i))

private theorem graphComposition {m k : Nat} (f : Program k) (g : Fin k → Program m) :
    OrdinaryArithmetic.graphFormula (Program.composition f g) =
      OrdinaryArithmetic.compositionGraph (OrdinaryArithmetic.graphFormula f)
        (fun i => OrdinaryArithmetic.graphFormula (g i)) := rfl

private theorem compF {m k : Nat} (f : Program k) (middle : List.Vector Nat k) (out : Nat)
    (ρ0 : Fin (m+1) ⊕ Fin k → Term 0) (β0 : Fin 0 → Term 0)
    (h0 : ρ0 (Sum.inl 0) = Term.numeral out)
    (hm : ∀ i, ρ0 (Sum.inr i) = Term.numeral (middle.get i)) :
    trB (OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula f)
      (FirstOrder.Language.Term.var (Sum.inl (0 : Fin (m+1))) :
        OrdinaryArithmetic.Term (Fin (m+1) ⊕ Fin k))
      (fun i => FirstOrder.Language.Term.var (Sum.inr i))) ρ0 β0 =
      GorbowOrdinaryArithmeticGraphs.closedGraph f middle out := by
  rw [closedGraphTr]
  refine (substBoundedTr _ _ ρ0 β0).trans
    (congrArg₂ (trB _) (funext fun a => ?_) (funext fun i => Fin.elim0 i))
  cases a using Fin.cases with
  | zero => exact h0
  | succ i => exact hm i

private theorem compG {m k : Nat} (g : Program m) (i : Fin k) (inputs : List.Vector Nat m) (mi : Nat)
    (ρ0 : Fin (m+1) ⊕ Fin k → Term 0) (β0 : Fin 0 → Term 0)
    (hi : ρ0 (Sum.inr i) = Term.numeral mi)
    (hin : ∀ j, ρ0 (Sum.inl j.succ) = Term.numeral (inputs.get j)) :
    trB (OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula g)
      (FirstOrder.Language.Term.var (Sum.inr i) : OrdinaryArithmetic.Term (Fin (m+1) ⊕ Fin k))
      (fun j => FirstOrder.Language.Term.var (Sum.inl j.succ))) ρ0 β0 =
      GorbowOrdinaryArithmeticGraphs.closedGraph g inputs mi := by
  rw [closedGraphTr]
  refine (substBoundedTr _ _ ρ0 β0).trans
    (congrArg₂ (trB _) (funext fun a => ?_) (funext fun j => Fin.elim0 j))
  cases a using Fin.cases with
  | zero => exact hi
  | succ j => exact hin j

private theorem bodyProof {T : Sentence → Prop} {m k : Nat} (f : Program k) (g : Fin k → Program m)
    (inputs : List.Vector Nat m) (middle : List.Vector Nat k) (out : Nat)
    (ρ0 : Fin (m+1) ⊕ Fin k → Term 0) (β0 : Fin 0 → Term 0)
    (h0 : ρ0 (Sum.inl 0) = Term.numeral out)
    (hm : ∀ i, ρ0 (Sum.inr i) = Term.numeral (middle.get i))
    (hin : ∀ j, ρ0 (Sum.inl j.succ) = Term.numeral (inputs.get j))
    (hf : Nonempty (Derivation T (GorbowOrdinaryArithmeticGraphs.closedGraph f middle out)))
    (hg : ∀ i, Nonempty (Derivation T
      (GorbowOrdinaryArithmeticGraphs.closedGraph (g i) inputs (middle.get i)))) :
    Nonempty (Derivation T (trB
      ((OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula f)
          (FirstOrder.Language.Term.var (Sum.inl (0 : Fin (m+1))) :
            OrdinaryArithmetic.Term (Fin (m+1) ⊕ Fin k))
          (fun i => FirstOrder.Language.Term.var (Sum.inr i))) ⊓
        OrdinaryArithmetic.andFin (fun i => OrdinaryArithmetic.applyGraph
          (OrdinaryArithmetic.graphFormula (g i))
          (FirstOrder.Language.Term.var (Sum.inr i) : OrdinaryArithmetic.Term (Fin (m+1) ⊕ Fin k))
          (fun j => FirstOrder.Language.Term.var (Sum.inl j.succ))))
      ρ0 β0)) := by
  obtain ⟨dF⟩ := hf
  have eF := compF f middle out ρ0 β0 h0 hm
  have hG : ∀ i, Nonempty (Derivation T (trB (OrdinaryArithmetic.applyGraph
      (OrdinaryArithmetic.graphFormula (g i))
      (FirstOrder.Language.Term.var (Sum.inr i) : OrdinaryArithmetic.Term (Fin (m+1) ⊕ Fin k))
      (fun j => FirstOrder.Language.Term.var (Sum.inl j.succ))) ρ0 β0)) := fun i =>
    (congrArg (fun x : Sentence => Nonempty (Derivation T x))
      (compG (g i) i inputs (middle.get i) ρ0 β0 (hm i) hin)).mpr (hg i)
  obtain ⟨dG⟩ := andFinTr ρ0 k _ β0 hG
  exact ⟨pairProof (cast (congrArg (fun x : Sentence => Derivation T x) eF.symm) dF) dG⟩

theorem compositionCertificates :
    GorbowArithmeticCompositionCertificates.Targets.CompositionCertificates := by
  intro T m k f g inputs middle out hf hg
  rw [closedGraphTr, graphComposition]
  unfold OrdinaryArithmetic.compositionGraph OrdinaryArithmetic.existsFin
  refine exsIntro _ (k + 0) _ (fun i : Fin (k + 0) => Term.numeral (middle.get i)) ?_
  rw [relabelTr]
  refine bodyProof f g inputs middle out _ _ ?_ ?_ ?_ hf hg
  · rfl
  · intro i; rfl
  · intro j; rfl

/-! ### The whole recursion-free fragment -/

theorem recursionFreeCertificates :
    GorbowArithmeticCompositionCertificates.Targets.RecursionFreeCertificates := by
  intro T n p
  induction p with
  | zero =>
    intro _ inputs
    rw [List.Vector.eq_nil inputs]
    exact GorbowOrdinaryArithmeticGraphs.Proof.initialCertificates.1 T
  | succ =>
    intro _ inputs
    have e : evaluate Program.succ inputs = inputs.get 0 + 1 :=
      (congrArg (· + 1) (List.Vector.get_zero inputs)).symm
    rw [e]
    exact GorbowOrdinaryArithmeticGraphs.Proof.initialCertificates.2.1 T inputs
  | projection i =>
    intro _ inputs
    exact GorbowOrdinaryArithmeticGraphs.Proof.initialCertificates.2.2 T _ i inputs
  | composition f g ihf ihg =>
    intro hp inputs
    obtain ⟨hpf, hpg⟩ := hp
    refine compositionCertificates T _ _ f g inputs (List.Vector.ofFn fun i => evaluate (g i) inputs)
      (evaluate f (List.Vector.ofFn fun i => evaluate (g i) inputs)) (ihf hpf _) (fun i => ?_)
    rw [List.Vector.get_ofFn]
    exact ihg i (hpg i) inputs
  | recursion f g _ _ =>
    intro hp
    exact False.elim hp

theorem fullTarget : GorbowArithmeticCompositionCertificates.Targets.Target :=
  ⟨witnessIntroduction, finiteConjunction, compositionCertificates, recursionFreeCertificates⟩

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates.Proof
