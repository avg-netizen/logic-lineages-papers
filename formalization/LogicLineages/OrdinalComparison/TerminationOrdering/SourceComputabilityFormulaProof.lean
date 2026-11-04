module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaProof
open FirstOrder Language Source SourceComputabilityFormula PositiveArithmeticOperators
open PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

def typedAt (typed : OrdinaryArithmetic.Formula (Fin 3)) (tau : Ty) : language.Formula (Fin 2) :=
  arithmeticEmbedding.onFormula (typed.subst ![.var 0, numeral (typeNumber tau), .var 1])

def appAt (app : OrdinaryArithmetic.Formula (Fin 6)) (sigma tau : Ty) :
    language.Formula ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) :=
  arithmeticEmbedding.onFormula (app.subst ![.var (.inl (.inl 0)), numeral (typeNumber sigma),
    numeral (typeNumber tau), .var (.inl (.inl 1)), .var (.inl (.inr 0)), .var (.inr 0)])

theorem typedAtTruth (typed : OrdinaryArithmetic.Formula (Fin 3)) (tau : Ty)
    (P : Nat → Prop) (context x : Nat) :
    realize P (typedAt typed tau) ![context,x] ↔ typed.Realize ![context,typeNumber tau,x] := by
  unfold typedAt
  rw [arithmeticSubstTruth]
  have hv : (fun i : Fin 3 =>
      (![(.var 0 : OrdinaryArithmetic.Term (Fin 2)), numeral (typeNumber tau), .var 1] i).realize ![context,x]) =
      ![context,typeNumber tau,x] := by
    funext i
    refine Fin.cases rfl (fun j => Fin.cases ?_ (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
    exact numeralTruth _ _
  rw [hv]

theorem appAtTruth (app : OrdinaryArithmetic.Formula (Fin 6)) (sigma tau : Ty)
    (P : Nat → Prop) (context x : Nat) (us zs : Fin 1 → Nat) :
    realize P (appAt app sigma tau) (Sum.elim (Sum.elim ![context,x] us) zs) ↔
      app.Realize ![context,typeNumber sigma,typeNumber tau,x,us 0,zs 0] := by
  unfold appAt
  rw [arithmeticSubstTruth]
  have hv : (fun i : Fin 6 =>
      (![(.var (.inl (.inl 0)) : OrdinaryArithmetic.Term ((Fin 2 ⊕ Fin 1) ⊕ Fin 1)),
        numeral (typeNumber sigma), numeral (typeNumber tau), .var (.inl (.inl 1)),
        .var (.inl (.inr 0)), .var (.inr 0)] i).realize (Sum.elim (Sum.elim ![context,x] us) zs)) =
      ![context,typeNumber sigma,typeNumber tau,x,us 0,zs 0] := by
    funext i
    refine Fin.cases rfl (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
      (fun l => Fin.cases rfl (fun m => Fin.cases rfl (fun o => Fin.cases rfl (fun p => Fin.elim0 p) o) m) l) k) j) i
    · exact numeralTruth _ _
    · exact numeralTruth _ _
  rw [hv]

theorem actualGeneralFormulaCalibration : SourceComputabilityFormulaTargets.ActualGeneralFormulaCalibration := by
  intro n arity Gamma
  obtain ⟨typed, htyped, _⟩ := OrdinaryArithmeticTypedCarrierProof.typedArithmeticFormula n arity Gamma
  obtain ⟨app, happ, _⟩ := OrdinaryArithmeticApplicationProof.partialApplicationFormula n arity Gamma
  have hex (tau : Ty) : ∃ phi : language.Formula (Fin 2),
      ∀ (P : Nat → Prop) (context x : Nat), realize P phi ![context,x] ↔ Computable n arity Gamma P context tau x := by
    induction tau with
    | ground =>
      refine ⟨typedAt typed .ground ⊓ (Positive.predicate (.var 1)).formula, ?_⟩
      intro P context x
      rw [generalConjTruth, typedAtTruth, htyped, predicateTruth]
      rfl
    | arrow sigma tau ihs iht =>
      obtain ⟨sp, hs⟩ := ihs
      obtain ⟨tp, ht⟩ := iht
      let domain : language.Formula (Fin 2 ⊕ Fin 1) := sp.relabel ![.inl 0, .inr 0]
      let codomain : language.Formula ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) := tp.relabel ![.inl (.inl 0), .inr 0]
      refine ⟨typedAt typed (.arrow sigma tau) ⊓ allOne (domain.imp (existsOne (appAt app sigma tau ⊓ codomain))), ?_⟩
      intro P context x
      have hdom (us : Fin 1 → Nat) : realize P domain (Sum.elim ![context,x] us) ↔
          Computable n arity Gamma P context sigma (us 0) := by
        dsimp [domain]
        rw [generalRelabelTruth]
        have hv : (Sum.elim ![context,x] us) ∘ ![Sum.inl 0, Sum.inr 0] = ![context,us 0] := by
          funext i
          exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
        rw [hv]
        exact hs P context (us 0)
      have hcod (us zs : Fin 1 → Nat) : realize P codomain (Sum.elim (Sum.elim ![context,x] us) zs) ↔
          Computable n arity Gamma P context tau (zs 0) := by
        dsimp [codomain]
        rw [generalRelabelTruth]
        have hv : (Sum.elim (Sum.elim ![context,x] us) zs) ∘ ![Sum.inl (Sum.inl 0), Sum.inr 0] = ![context,zs 0] := by
          funext i
          exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
        rw [hv]
        exact ht P context (zs 0)
      rw [generalConjTruth, typedAtTruth, htyped, allOneTruth]
      simp only [generalImpTruth, hdom, existsOneTruth, generalConjTruth, appAtTruth, happ, hcod]
      change (_ ∧ ∀ us : Fin 1 → Nat, _ → ∃ zs : Fin 1 → Nat, _) ↔
        (_ ∧ ∀ u : Nat, _ → ∃ z : Nat, _)
      constructor
      · rintro ⟨hc, h⟩
        refine ⟨hc, ?_⟩
        intro u hu
        obtain ⟨zs, hz⟩ := h (fun _ => u) hu
        exact ⟨zs 0, hz⟩
      · rintro ⟨hc, h⟩
        refine ⟨hc, ?_⟩
        intro us hu
        obtain ⟨z, hz⟩ := h (us 0) hu
        exact ⟨fun _ => z, hz⟩
  classical
  exact ⟨fun tau => Classical.choose (hex tau), fun tau => Classical.choose_spec (hex tau)⟩

theorem actualComputabilityTypedness : SourceComputabilityFormulaTargets.ActualComputabilityTypedness := by
  intro n arity Gamma P context tau x h
  cases tau <;> exact h.1

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaProof
