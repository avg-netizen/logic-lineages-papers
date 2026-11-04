module

public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
/-! The ordinary-arithmetic graph bridge into actual Gorbow syntax. Term and
bounded-formula translations land in the visible 0/S/+/* equality image and are
truth-preserving in every interpretation; at each quantifier the translator's
lastCases map converts Mathlib's new-last bound level into Gorbow's new-first
index, retaining all older variables. The paid program graph semantics then
gives actual graph truth and all primitive-recursive graphs, and the three
initial constructors have literal reflexivity derivations over any closed
theory. No graph-correctness axiom or internal HB is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

/-! ### Terms -/

theorem termImage : GorbowOrdinaryArithmeticGraphs.Targets.TermImage := by
  intro alpha m rho t
  induction t with
  | var i => exact .var _
  | func f ts ih =>
    cases f with
    | zero => exact .zero
    | succ => exact .succ (ih 0)
    | add => exact .add (ih 0) (ih 1)
    | mul => exact .mul (ih 0) (ih 1)

theorem termTruth : GorbowOrdinaryArithmeticGraphs.Targets.TermTruth := by
  intro alpha m I rho t v
  induction t with
  | var i => rfl
  | func f ts ih =>
    cases f with
    | zero => rfl
    | succ => exact congrArg Nat.succ (ih 0)
    | add => exact congrArg₂ (· + ·) (ih 0) (ih 1)
    | mul => exact congrArg₂ (· * ·) (ih 0) (ih 1)

/-! ### Bounded formulas -/

private theorem formulaImageAux {alpha : Type} {l : Nat}
    (a : OrdinaryArithmetic.arithmeticLanguage.BoundedFormula alpha l) :
    ∀ {m : Nat} (free : alpha → Fin m) (bound : Fin l → Fin m),
      ArithmeticFormula (translateBounded a free bound) := by
  induction a with
  | falsum => intro m free bound; exact .neg (.equal .zero .zero)
  | equal t u => intro m free bound; exact .equal (termImage _ _ _ t) (termImage _ _ _ u)
  | rel r _ => exact Empty.elim r
  | imp a b iha ihb => intro m free bound; exact .imp (iha free bound) (ihb free bound)
  | all a ih => intro m free bound; exact .all (ih _ _)

theorem formulaImage : GorbowOrdinaryArithmeticGraphs.Targets.FormulaImage := by
  intro alpha l m a free bound
  exact formulaImageAux a free bound

private theorem snocAgree {l m : Nat} (bound : Fin l → Fin m) (v : Fin m → Nat) (x : Nat) :
    (fun i => (Fin.cases x v : Fin (m+1) → Nat)
      ((Fin.lastCases (0 : Fin (m+1)) (fun i => (bound i).succ) : Fin (l+1) → Fin (m+1)) i)) =
      Fin.snoc (fun i => v (bound i)) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last, Fin.snoc_last, Fin.cases_zero]
  · simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.cases_succ]

private theorem boundedTruthAux {alpha : Type} {l : Nat}
    (a : OrdinaryArithmetic.arithmeticLanguage.BoundedFormula alpha l) (I : Interpretation) :
    ∀ {m : Nat} (free : alpha → Fin m) (bound : Fin l → Fin m) (v : Fin m → Nat),
      (translateBounded a free bound).realize I v ↔
        a.Realize (fun i => v (free i)) (fun i => v (bound i)) := by
  induction a with
  | falsum =>
    intro m free bound v
    exact ⟨fun h => h rfl, fun h => False.elim h⟩
  | equal t u =>
    intro m free bound v
    have he : (fun i => v (Sum.elim free bound i)) =
        Sum.elim (fun i => v (free i)) (fun i => v (bound i)) := by
      funext i; cases i <;> rfl
    have h1 : (translateTerm (Sum.elim free bound) t).realize I v =
        FirstOrder.Language.Term.realize (Sum.elim (fun i => v (free i)) (fun i => v (bound i))) t :=
      (termTruth _ _ I _ t v).trans (congrArg (fun w => FirstOrder.Language.Term.realize w t) he)
    have h2 : (translateTerm (Sum.elim free bound) u).realize I v =
        FirstOrder.Language.Term.realize (Sum.elim (fun i => v (free i)) (fun i => v (bound i))) u :=
      (termTruth _ _ I _ u v).trans (congrArg (fun w => FirstOrder.Language.Term.realize w u) he)
    exact ⟨fun h => Eq.trans h1.symm (Eq.trans h h2), fun h => Eq.trans h1 (Eq.trans h h2.symm)⟩
  | rel r _ => exact Empty.elim r
  | imp a b iha ihb =>
    intro m free bound v
    exact imp_congr (iha free bound v) (ihb free bound v)
  | all a ih =>
    intro m free bound v
    refine forall_congr' (fun x => ?_)
    have h := ih (fun i => (free i).succ) (Fin.lastCases 0 (fun i => (bound i).succ)) (Fin.cases x v)
    have hf : (fun i => (Fin.cases x v : Fin (m+1) → Nat) ((free i).succ)) = (fun i => v (free i)) := by
      funext i; rfl
    exact h.trans (Iff.of_eq (congrArg₂ (fun V xs => FirstOrder.Language.BoundedFormula.Realize a V xs)
      hf (snocAgree bound v x)))

theorem boundedTruth : GorbowOrdinaryArithmeticGraphs.Targets.BoundedTruth := by
  intro alpha l m I a free bound v
  exact boundedTruthAux a I free bound v

/-! ### Actual program graphs -/

theorem programTruth : GorbowOrdinaryArithmeticGraphs.Targets.ProgramTruth := by
  intro n p I v
  have h := boundedTruthAux (OrdinaryArithmetic.graphFormula p) I id Fin.elim0 v
  have hp := OrdinaryArithmeticProgramProof.programGraphTruth p v
  unfold FirstOrder.Language.Formula.Realize at hp
  have he : (fun i : Fin 0 => v (Fin.elim0 i)) =
      (@default (Fin 0 → Nat) Unique.instInhabited) := by
    funext i
    exact Fin.elim0 i
  exact h.trans ((Iff.of_eq (congrArg
    (fun xs => FirstOrder.Language.BoundedFormula.Realize (OrdinaryArithmetic.graphFormula p) v xs) he)).trans hp)

theorem allPrimitiveGraphs : GorbowOrdinaryArithmeticGraphs.Targets.AllPrimitiveGraphs := by
  intro n f hf
  obtain ⟨p, hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions n f hf
  refine ⟨graph p, formulaImageAux (OrdinaryArithmetic.graphFormula p) id Fin.elim0, fun I v => ?_⟩
  exact (programTruth n p I v).trans (Iff.of_eq (congrArg (· = v 0) (hp _)))

/-! ### Literal initial certificates -/

theorem initialCertificates : GorbowOrdinaryArithmeticGraphs.Targets.InitialCertificates :=
  ⟨fun _ => ⟨.logical (.reflexive .zero)⟩,
    fun _ inputs => ⟨.logical (.reflexive (.succ (Term.numeral (inputs.get 0))))⟩,
    fun _ _ i inputs => ⟨.logical (.reflexive (Term.numeral (inputs.get i)))⟩⟩

theorem fullTarget : GorbowOrdinaryArithmeticGraphs.Targets.Target :=
  ⟨termImage, formulaImage, termTruth, boundedTruth, programTruth, allPrimitiveGraphs,
    initialCertificates⟩

end LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphs.Proof
