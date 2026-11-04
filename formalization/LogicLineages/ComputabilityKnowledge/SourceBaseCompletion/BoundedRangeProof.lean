module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructureProof
public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof

@[expose] public section
/-! Fixed finite-range elimination for the literal compiled arithmetic guard.
The guard is shown to be literally the implication/falsum encoding of
exists d, x+S(d)=bound. Range elimination is an actual PA derivation, by
internal induction on x of the finite conjunction of the range statements for
all smaller external bounds, using the paid R026 left-successor theorem, PA
successor axioms and equality logic. Bounded generalization combines it with
actual proofs of the numeral instances of an arbitrary full-language matrix.
A local one-hypothesis proof compiler uses only K/S/MP and is discharged
before every generalization; it is not a new rule. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange.Proof
open GorbowSyntax GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

/-! ### Hilbert combinators and a one-hypothesis compiler (as in R026) -/

private def idProof (A : Sentence → Prop) {n : Nat} (a : Formula n) : Derivation A (.imp a a) :=
  .mp (.mp (.logical (.s a (.imp a a) a)) (.logical (.k a (.imp a a)))) (.logical (.k a a))

private def liftP {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) :=
  .mp (.logical (.k a r)) p

private def sApp {A : Sentence → Prop} {n : Nat} {x y z : Formula n}
    (p : Derivation A (.imp x (.imp y z))) (q : Derivation A (.imp x y)) : Derivation A (.imp x z) :=
  .mp (.mp (.logical (.s x y z)) p) q

private def compose {A : Sentence → Prop} {n : Nat} {a b c : Formula n}
    (p : Derivation A (.imp b c)) (q : Derivation A (.imp a b)) : Derivation A (.imp a c) :=
  .mp (.mp (.logical (.s a b c)) (liftP a p)) q

private inductive Under (T : Sentence → Prop) {n : Nat} (R : Formula n) : Formula n → Type where
  | hyp : Under T R R
  | known {φ : Formula n} : Derivation T φ → Under T R φ
  | mp {a b : Formula n} : Under T R (.imp a b) → Under T R a → Under T R b

private def compileU {T : Sentence → Prop} {n : Nat} {R : Formula n} :
    {φ : Formula n} → Under T R φ → Derivation T (.imp R φ)
  | _, .hyp => idProof T R
  | _, .known d => liftP R d
  | _, .mp p q => sApp (compileU p) (compileU q)

private def castU {T : Sentence → Prop} {n : Nat} {R φ ψ : Formula n} (e : φ = ψ)
    (p : Under T R φ) : Under T R ψ :=
  cast (congrArg (Under T R) e) p

private def uComp {T : Sentence → Prop} {n : Nat} {R a b c : Formula n}
    (p : Under T R (.imp b c)) (q : Under T R (.imp a b)) : Under T R (.imp a c) :=
  .mp (.mp (.known (.logical (.s a b c))) (.mp (.known (.logical (.k (.imp b c) a))) p)) q

private def exFalso (T : Sentence → Prop) {n : Nat} (a b : Formula n) :
    Derivation T (.imp (.neg a) (.imp a b)) :=
  compose (.logical (.classicalContraposition b a)) (.logical (.k (.neg a) (.neg b)))

private def uExFalso {T : Sentence → Prop} {n : Nat} {R a b : Formula n}
    (hn : Under T R (.neg a)) (ha : Under T R a) : Under T R b :=
  .mp (.mp (.known (exFalso T a b)) hn) ha

/-! ### Open-context equality (as in R026) -/

private theorem cancel {n : Nat} (s t : Term n) :
    GorbowSubstitution.substitute (Fin.cases s Term.var : Fin (n+1) → Term n)
      (GorbowFormulaSubstitution.renameTerm Fin.succ t) = t := by
  unfold GorbowFormulaSubstitution.renameTerm
  rw [GorbowSubstitution.substitute_composition]
  exact GorbowSubstitution.substitute_variables t

private def uRefl {T : Sentence → Prop} {n : Nat} {R : Formula n} (t : Term n) :
    Under T R (.equal t t) :=
  .known (.logical (.reflexive t))

private def uReplace {T : Sentence → Prop} {n : Nat} {R : Formula n} (a : Formula (n+1))
    {t u : Term n} (h : Under T R (.equal t u))
    (q : Under T R (GorbowStandardInstances.instantiate a t)) :
    Under T R (GorbowStandardInstances.instantiate a u) :=
  .mp (.mp (.known (.logical (.equalityReplace a t u))) h) q

private def uSymm {T : Sentence → Prop} {n : Nat} {R : Formula n} {t u : Term n}
    (h : Under T R (.equal t u)) : Under T R (.equal u t) :=
  castU (congrArg (Formula.equal u) (cancel u t))
    (uReplace (.equal (.var 0) (GorbowFormulaSubstitution.renameTerm Fin.succ t)) h
      (castU (congrArg (Formula.equal t) (cancel t t)).symm (uRefl t)))

private def uTrans {T : Sentence → Prop} {n : Nat} {R : Formula n} {t u v : Term n}
    (h1 : Under T R (.equal t u)) (h2 : Under T R (.equal u v)) : Under T R (.equal t v) :=
  castU (congrArg (fun x => Formula.equal x v) (cancel v t))
    (uReplace (.equal (GorbowFormulaSubstitution.renameTerm Fin.succ t) (.var 0)) h2
      (castU (congrArg (fun x => Formula.equal x u) (cancel u t)).symm h1))

private def uSuccCongr {T : Sentence → Prop} {n : Nat} {R : Formula n} {t u : Term n}
    (h : Under T R (.equal t u)) : Under T R (.equal (.succ t) (.succ u)) :=
  castU (congrArg (fun x => Formula.equal (.succ x) (.succ u)) (cancel u t))
    (uReplace (.equal (.succ (GorbowFormulaSubstitution.renameTerm Fin.succ t)) (.succ (.var 0))) h
      (castU (congrArg (fun x => Formula.equal (.succ x) (.succ t)) (cancel t t)).symm
        (uRefl (.succ t))))

/-! ### Substitution identity (as in R024) -/

private theorem liftVar (n : Nat) :
    GorbowFormulaSubstitution.liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaIdentity {n : Nat} (φ : Formula n) :
    GorbowFormulaSubstitution.substituteFormula Term.var φ = φ := by
  induction φ <;> simp only [GorbowFormulaSubstitution.substituteFormula,
    GorbowSubstitution.substitute_variables, liftVar, *]

/-! ### The literal compiled guard -/

private theorem relabelNum {α β : Type} (g : α → β) : ∀ b : Nat,
    FirstOrder.Language.Term.relabel g (ordinaryNumeral b : OrdinaryArithmetic.Term α) =
      ordinaryNumeral b
  | 0 => congrArg (FirstOrder.Language.Term.func (L := OrdinaryArithmetic.arithmeticLanguage)
      OrdinaryArithmetic.FunctionSymbol.zero) (funext fun i => Fin.elim0 i)
  | b+1 => congrArg (FirstOrder.Language.Term.func (L := OrdinaryArithmetic.arithmeticLanguage)
      OrdinaryArithmetic.FunctionSymbol.succ) (funext fun i => by
        cases i using Fin.cases with
        | zero => exact relabelNum g b
        | succ j => exact Fin.elim0 j)

private theorem transNum {α : Type} {m : Nat} (ρ : α → Fin m) : ∀ b : Nat,
    GorbowOrdinaryArithmeticGraphs.translateTerm ρ (ordinaryNumeral b) = Term.numeral b
  | 0 => rfl
  | b+1 => congrArg Term.succ (transNum ρ b)

private def gRho : Fin 1 ⊕ Fin (0+1) → Fin (1+1) :=
  Sum.elim (fun i : Fin 1 => (id i).succ)
    (Fin.lastCases (0 : Fin (1+1)) (fun i : Fin 0 => ((Fin.elim0 : Fin 0 → Fin 1) i).succ))

private def gRel : (Fin 1 ⊕ Fin 1) ⊕ Fin 0 → Fin 1 ⊕ Fin (1+0) :=
  FirstOrder.Language.BoundedFormula.relabelAux (id : Fin 1 ⊕ Fin 1 → Fin 1 ⊕ Fin 1) 0

private def falseF {n : Nat} : Formula n := .neg (.equal .zero .zero)

private def gL (m : Nat) : Fin (1+1) → Term (m+1+1) :=
  GorbowFormulaSubstitution.liftSubstitute (fun _ : Fin 1 => (Term.var 0 : Term (m+1)))

private def gShape (m : Nat) (xi di : Fin (1+1)) (N : Term (1+1)) : Formula (m+1) :=
  .imp (.all (.imp (.equal (.add (GorbowSubstitution.substitute (gL m) (.var xi))
      (.succ (GorbowSubstitution.substitute (gL m) (.var di))))
      (GorbowSubstitution.substitute (gL m) N)) falseF)) falseF

theorem compilerGuard : Targets.CompilerGuard := by
  intro m bound
  have h1 : guard (m := m) bound = gShape m (gRho (gRel (Sum.inl (Sum.inl 0))))
      (gRho (gRel (Sum.inl (Sum.inr 0))))
      (GorbowOrdinaryArithmeticGraphs.translateTerm gRho
        (FirstOrder.Language.Term.relabel gRel
          (FirstOrder.Language.Term.relabel (Sum.inl : Fin 1 ⊕ Fin 1 → (Fin 1 ⊕ Fin 1) ⊕ Fin 0)
            (FirstOrder.Language.Term.relabel (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)
              (ordinaryNumeral bound : OrdinaryArithmetic.Term (Fin 1)))))) := rfl
  have hx : gRho (gRel (Sum.inl (Sum.inl 0))) = 1 := by
    decide
  have hd : gRho (gRel (Sum.inl (Sum.inr 0))) = 0 := by
    decide
  rw [h1, hx, hd, relabelNum, relabelNum, relabelNum, transNum]
  exact congrArg (fun N : Term (m+1+1) => (Formula.imp (.all (.imp (.equal (.add (.var 1)
    (.succ (.var 0))) N) falseF)) falseF : Formula (m+1)))
    (GorbowHeaderSubstitutionProof.numerals _ _ (gL m) bound)

theorem guardSemantics : Targets.GuardSemantics := by
  intro m bound I env
  rw [compilerGuard m bound]
  have key : ∀ d : Nat, (Term.numeral bound : Term (m+1+1)).realize I (Fin.cases d env) = bound :=
    fun d => numeral_realize _ _ _
  constructor
  · intro h
    by_contra hlt
    exact h (fun d hd => absurd (show env 0 < bound by
      change env 0 + Nat.succ d = (Term.numeral bound : Term (m+1+1)).realize I (Fin.cases d env) at hd
      rw [key d] at hd
      omega) hlt) rfl
  · intro hlt h hz
    have hE : env 0 + Nat.succ (bound - env 0 - 1) =
        (Term.numeral bound : Term (m+1+1)).realize I (Fin.cases (bound - env 0 - 1) env) := by
      rw [key]
      omega
    exact h (bound - env 0 - 1) hE hz

/-! ### Finite disjunctions -/

private def disjList {n : Nat} (l : List (Formula n)) : Formula n := l.foldr Formula.disj falseF

private theorem disjZero {n : Nat} (f : Fin 0 → Formula n) : disjList (List.ofFn f) = falseF := by
  simp only [disjList, List.ofFn_zero, List.foldr_nil]

private theorem disjCons {n k : Nat} (f : Fin (k+1) → Formula n) :
    disjList (List.ofFn f) = .disj (f 0) (disjList (List.ofFn (fun i => f i.succ))) := by
  simp only [disjList, List.ofFn_succ, List.foldr_cons]

private theorem substDisj {n n' : Nat} (σ : Fin n → Term n') : ∀ l : List (Formula n),
    GorbowFormulaSubstitution.substituteFormula σ (disjList l) =
      disjList (l.map (GorbowFormulaSubstitution.substituteFormula σ))
  | [] => rfl
  | a :: l => congrArg (Formula.disj (GorbowFormulaSubstitution.substituteFormula σ a)) (substDisj σ l)

private def dMap (T : Sentence → Prop) {n : Nat} : ∀ (k : Nat) (f g : Fin k → Formula n),
    (∀ i, Derivation T (.imp (f i) (g i))) →
      Derivation T (.imp (disjList (List.ofFn f)) (disjList (List.ofFn g)))
  | 0, f, g, _ => cast (by rw [disjZero f, disjZero g]) (idProof T (falseF : Formula n))
  | k+1, f, g, h => cast (by rw [disjCons f, disjCons g])
      (Derivation.mp (.mp (.logical (.orElim (f 0) _ (.disj (g 0) (disjList (List.ofFn (fun i => g i.succ))))))
        (compose (.logical (.orLeft (g 0) _)) (h 0)))
        (compose (.logical (.orRight (g 0) _))
          (dMap T k (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))))

private def dElim (T : Sentence → Prop) {n : Nat} : ∀ (k : Nat) (f : Fin k → Formula n)
    (ψ : Formula n), (∀ i, Derivation T (.imp (f i) ψ)) →
      Derivation T (.imp (disjList (List.ofFn f)) ψ)
  | 0, f, ψ, _ => cast (congrArg (fun X => Derivation T (.imp X ψ)) (disjZero f).symm)
      (compileU (R := (falseF : Formula n)) (uExFalso .hyp (uRefl .zero)))
  | k+1, f, ψ, h => cast (congrArg (fun X => Derivation T (.imp X ψ)) (disjCons f).symm)
      (.mp (.mp (.logical (.orElim (f 0) _ ψ)) (h 0))
        (dElim T k (fun i => f i.succ) ψ (fun i => h i.succ)))

/-! ### Guard and range at an arbitrary point -/

private def guardAt {n : Nat} (t : Term n) (k : Nat) : Formula n :=
  .imp (.all (.imp (.equal (.add (GorbowFormulaSubstitution.renameTerm Fin.succ t) (.succ (.var 0)))
    (Term.numeral k)) falseF)) falseF

private def casesAt {n : Nat} (t : Term n) (k : Nat) : Formula n :=
  disjList (List.ofFn (fun i : Fin k => Formula.equal t (Term.numeral i.val)))

private def hAt {n : Nat} (t : Term n) (k : Nat) : Formula n := .imp (guardAt t k) (casesAt t k)

private def psi {n : Nat} (t : Term n) : Nat → Formula n
  | 0 => hAt t 0
  | b+1 => .conj (psi t b) (hAt t (b+1))

private theorem substGuard {n n' : Nat} (σ : Fin (n+1) → Term n') (k : Nat) :
    GorbowFormulaSubstitution.substituteFormula σ (guardAt (.var 0) k) = guardAt (σ 0) k :=
  congrArg (fun N : Term (n'+1) => (Formula.imp (.all (.imp (.equal (.add
      (GorbowFormulaSubstitution.renameTerm Fin.succ (σ 0)) (.succ (.var 0))) N) falseF))
      falseF : Formula n'))
    (GorbowHeaderSubstitutionProof.numerals _ _ (GorbowFormulaSubstitution.liftSubstitute σ) k)

private theorem substCases {n n' : Nat} (σ : Fin (n+1) → Term n') (k : Nat) :
    GorbowFormulaSubstitution.substituteFormula σ (casesAt (.var 0) k) = casesAt (σ 0) k := by
  unfold casesAt
  rw [substDisj, List.map_ofFn]
  exact congrArg (fun F => disjList (List.ofFn F)) (funext fun i =>
    congrArg (Formula.equal (σ 0)) (GorbowHeaderSubstitutionProof.numerals _ _ σ i.val))

private theorem substH {n n' : Nat} (σ : Fin (n+1) → Term n') (k : Nat) :
    GorbowFormulaSubstitution.substituteFormula σ (hAt (.var 0) k) = hAt (σ 0) k :=
  congrArg₂ Formula.imp (substGuard σ k) (substCases σ k)

private theorem substPsi {n n' : Nat} (σ : Fin (n+1) → Term n') :
    ∀ b : Nat, GorbowFormulaSubstitution.substituteFormula σ (psi (.var 0) b) = psi (σ 0) b
  | 0 => substH σ 0
  | b+1 => congrArg₂ Formula.conj (substPsi σ b) (substH σ (b+1))

private def refuteGuard (T : Sentence → Prop) {n : Nat} (t : Term n) :
    Derivation T (.imp (guardAt t 0) falseF) :=
  compileU (R := guardAt t 0) (.mp .hyp (.known (.generalize
    (compileU (R := (.equal (.add (GorbowFormulaSubstitution.renameTerm Fin.succ t) (.succ (.var 0)))
        .zero : Formula (n+1)))
      (uExFalso (b := falseF)
        (.known (.arithmetic (.succNotZero (.add (GorbowFormulaSubstitution.renameTerm Fin.succ t)
          (.var 0)))))
        (uTrans (uSymm (.known (.arithmetic (.addSucc
          (GorbowFormulaSubstitution.renameTerm Fin.succ t) (.var 0))))) .hyp))))))

private def lsFormula (m : Nat) : Formula (m+2) :=
  .equal (.add (.succ (.var 1)) (.var 0)) (.succ (.add (.var 1) (.var 0)))

private def e10 (T : Sentence → Prop) {m : Nat} (ls : Derivation T (lsFormula m)) (k : Nat) :
    Derivation T (.imp (.equal (.add (.succ (.var 1)) (.succ (.var 0))) (Term.numeral (k+1)) :
        Formula (m+2))
      (.equal (.add (.var 1) (.succ (.var 0))) (Term.numeral k))) :=
  compileU (R := (.equal (.add (.succ (.var 1)) (.succ (.var 0))) (Term.numeral (k+1)) : Formula (m+2)))
    (uTrans (.known (.arithmetic (.addSucc (.var 1) (.var 0))))
      (.mp (.known (.arithmetic (.succInjective (.succ (.add (.var 1) (.var 0))) (Term.numeral k))))
        (uTrans (uSymm (uTrans (.known (.arithmetic (.addSucc (.succ (.var 1)) (.var 0))))
          (uSuccCongr (.known ls)))) .hyp)))

private def guardShift (T : Sentence → Prop) {m : Nat} (ls : Derivation T (lsFormula m)) (k : Nat) :
    Derivation T (.imp (guardAt (.succ (.var 0) : Term (m+1)) (k+1)) (guardAt (.var 0) k)) :=
  compileU (R := guardAt (.succ (.var 0) : Term (m+1)) (k+1))
    (uComp .hyp (.known (.mp (.logical (.allDistribute _ _)) (.generalize
      (compileU (R := (.imp (.equal (.add (.var 1) (.succ (.var 0))) (Term.numeral k)) falseF :
          Formula (m+2)))
        (uComp .hyp (.known (e10 T ls k))))))))

private def casesShift (T : Sentence → Prop) {m : Nat} (k : Nat) :
    Derivation T (.imp (casesAt (.var 0 : Term (m+1)) k) (casesAt (.succ (.var 0)) (k+1))) :=
  cast (congrArg (fun X => Derivation T (.imp (casesAt (.var 0 : Term (m+1)) k) X))
      (disjCons (fun i : Fin (k+1) =>
        Formula.equal (.succ (.var 0) : Term (m+1)) (Term.numeral i.val))).symm)
    (compose (.logical (.orRight (Formula.equal (.succ (.var 0) : Term (m+1)) (Term.numeral 0)) _))
      (dMap T k (fun i : Fin k => Formula.equal (.var 0 : Term (m+1)) (Term.numeral i.val))
        (fun i : Fin k => Formula.equal (.succ (.var 0) : Term (m+1)) (Term.numeral (Fin.succ i).val))
        (fun _ => compileU (uSuccCongr .hyp))))

private def succTransfer (T : Sentence → Prop) {m : Nat} (ls : Derivation T (lsFormula m))
    (k : Nat) :
    Derivation T (.imp (hAt (.var 0 : Term (m+1)) k) (hAt (.succ (.var 0)) (k+1))) :=
  compileU (R := hAt (.var 0 : Term (m+1)) k)
    (uComp (.known (casesShift T k)) (uComp .hyp (.known (guardShift T ls k))))

private def psiProj (T : Sentence → Prop) {n : Nat} (t : Term n) :
    ∀ b : Nat, Derivation T (.imp (psi t b) (hAt t b))
  | 0 => idProof T _
  | _+1 => .logical (.andRight _ _)

private def psiZero (T : Sentence → Prop) {m : Nat} : ∀ b : Nat, Derivation T (psi (.zero : Term m) b)
  | 0 => cast (congrArg (fun X => Derivation T (.imp (guardAt (.zero : Term m) 0) X))
      (disjZero (fun i : Fin 0 => Formula.equal (.zero : Term m) (Term.numeral i.val))).symm)
      (refuteGuard T .zero)
  | b+1 => .mp (.mp (.logical (.andIntro _ _)) (psiZero T b))
      (cast (congrArg (fun X => Derivation T (.imp (guardAt (.zero : Term m) (b+1)) X))
          (disjCons (fun i : Fin (b+1) =>
            Formula.equal (.zero : Term m) (Term.numeral i.val))).symm)
        (liftP _ (.mp (.logical (.orLeft (Formula.equal (.zero : Term m) (Term.numeral 0)) _))
          (.logical (.reflexive .zero)))))

private def psiStep (T : Sentence → Prop) {m : Nat} (ls : Derivation T (lsFormula m)) :
    ∀ b : Nat, Derivation T (.imp (psi (.var 0 : Term (m+1)) b) (psi (.succ (.var 0)) b))
  | 0 => liftP _ (cast (congrArg (fun X => Derivation T
      (.imp (guardAt (.succ (.var 0) : Term (m+1)) 0) X))
      (disjZero (fun i : Fin 0 =>
        Formula.equal (.succ (.var 0) : Term (m+1)) (Term.numeral i.val))).symm)
      (refuteGuard T (.succ (.var 0))))
  | b+1 => compileU (R := psi (.var 0 : Term (m+1)) (b+1))
      (.mp (.mp (.known (.logical (.andIntro _ _)))
          (.mp (.known (psiStep T ls b)) (.mp (.known (.logical (.andLeft _ _))) .hyp)))
        (.mp (.known (succTransfer T ls b))
          (.mp (.known (psiProj T _ b)) (.mp (.known (.logical (.andLeft _ _))) .hyp))))

/-! ### Range elimination -/

theorem rangeElimination : Targets.RangeElimination := by
  intro T m bound
  obtain ⟨L0⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _
    (GorbowPAAdditiveStructure.Proof.leftSuccessor T) (m+2)
  have ls : Derivation T (lsFormula m) :=
    .mp (.logical (.allInstantiate _ (.var 0))) (.mp (.logical (.allInstantiate _ (.var 1))) L0)
  have base : Derivation T (GorbowStandardInstances.instantiate (psi (.var 0 : Term (m+1)) bound) .zero) :=
    cast (congrArg (fun X : Formula m => Derivation T X)
      (substPsi (Fin.cases (.zero : Term m) Term.var) bound).symm) (psiZero T bound)
  have step : Derivation T (.imp (psi (.var 0 : Term (m+1)) bound)
      (GorbowStandardInduction.successorInstance (psi (.var 0 : Term (m+1)) bound))) :=
    cast (congrArg (fun X => Derivation T (.imp (psi (.var 0 : Term (m+1)) bound) X))
      (substPsi (Fin.cases (.succ (.var 0)) (fun i : Fin m => Term.var i.succ)) bound).symm)
      (psiStep T ls bound)
  have hInd : Derivation T (.all (psi (.var 0 : Term (m+1)) bound)) :=
    .mp (.mp (.arithmetic (.induction (psi (.var 0 : Term (m+1)) bound))) base) (.generalize step)
  have hall : Derivation T (.all (hAt (.var 0 : Term (m+1)) bound)) :=
    .mp (.mp (.logical (.allDistribute _ _)) (.generalize (psiProj T (.var 0 : Term (m+1)) bound))) hInd
  rw [compilerGuard m bound]
  exact ⟨hall⟩

/-! ### Bounded generalization for an arbitrary full-language matrix -/

private def shiftDict (m : Nat) : Fin (m+1) → Term (m+2) :=
  Fin.cases (.var 0) (fun j : Fin m => .var j.succ.succ)

private def aOf {m : Nat} (phi : Formula (m+1)) : Formula (m+2) :=
  GorbowFormulaSubstitution.substituteFormula (shiftDict m) phi

private theorem instA {m : Nat} (phi : Formula (m+1)) (t : Term (m+1)) :
    GorbowStandardInstances.instantiate (aOf phi) t =
      GorbowFormulaSubstitution.substituteFormula (Fin.cases t (fun j : Fin m => Term.var j.succ)) phi :=
  (GorbowFormulaCompositionProof.composition _ _ _ phi _ _).trans
    (congrArg (fun s => GorbowFormulaSubstitution.substituteFormula s phi) (funext fun j => by
      cases j using Fin.cases with
      | zero => rfl
      | succ j => rfl))

private theorem instAvar {m : Nat} (phi : Formula (m+1)) :
    GorbowStandardInstances.instantiate (aOf phi) (.var 0) = phi := by
  have he : (Fin.cases (.var 0) (fun j : Fin m => Term.var j.succ) : Fin (m+1) → Term (m+1)) =
      Term.var := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  exact (instA phi (.var 0)).trans
    ((congrArg (fun s => GorbowFormulaSubstitution.substituteFormula s phi) he).trans
      (formulaIdentity phi))

private theorem weakInst {m : Nat} (phi : Formula (m+1)) (i : Nat) :
    GorbowFormulaSubstitution.substituteFormula (fun j : Fin m => (Term.var j.succ : Term (m+1)))
      (GorbowStandardInstances.instantiate phi (Term.numeral i)) =
    GorbowStandardInstances.instantiate (aOf phi) (Term.numeral i) := by
  rw [instA]
  unfold GorbowStandardInstances.instantiate
  rw [GorbowFormulaCompositionProof.composition]
  exact congrArg (fun s => GorbowFormulaSubstitution.substituteFormula s phi) (funext fun j => by
    cases j using Fin.cases with
    | zero => exact GorbowHeaderSubstitutionProof.numerals _ _ _ i
    | succ j => rfl)

private def caseProof (T : Sentence → Prop) {m : Nat} (phi : Formula (m+1)) (i : Nat)
    (w : Derivation T (GorbowStandardInstances.instantiate (aOf phi) (Term.numeral i))) :
    Derivation T (.imp (.equal (.var 0) (Term.numeral i)) phi) :=
  cast (congrArg (fun X => Derivation T (.imp (.equal (.var 0) (Term.numeral i)) X)) (instAvar phi))
    (compileU (R := (.equal (.var 0) (Term.numeral i) : Formula (m+1)))
      (.mp (.mp (.known (.logical (.equalityReplace (aOf phi) (Term.numeral i) (.var 0))))
        (uSymm .hyp)) (.known w)))

theorem boundedGeneralization : Targets.BoundedGeneralization := by
  intro T m bound phi h
  obtain ⟨hR⟩ := rangeElimination T m bound
  have hw : ∀ i : Fin bound,
      Derivation T (GorbowStandardInstances.instantiate (aOf phi) (Term.numeral i.val)) := fun i =>
    cast (congrArg (fun X : Formula (m+1) => Derivation T X) (weakInst phi i.val))
      (Classical.choice (GorbowDerivationSubstitution.Proof.derivationSubstitution T m (m+1) _
        (fun j : Fin m => Term.var j.succ) (h i)))
  have hc : Derivation T (.imp (casesBelow (m := m) bound) phi) :=
    dElim T bound (fun i : Fin bound => (Formula.equal (.var 0) (Term.numeral i.val) : Formula (m+1)))
      phi (fun i => caseProof T phi i.val (hw i))
  have hstep : Derivation T (.imp (.imp (guard (m := m) bound) (casesBelow bound))
      (.imp (guard (m := m) bound) phi)) :=
    compileU (R := .imp (guard (m := m) bound) (casesBelow bound)) (uComp (.known hc) .hyp)
  exact ⟨.mp (.mp (.logical (.allDistribute _ _)) (.generalize hstep)) hR⟩

theorem fullTarget : Targets.Target :=
  ⟨compilerGuard, guardSemantics, rangeElimination, boundedGeneralization⟩

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange.Proof
