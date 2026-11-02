module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueProof
open Source Source.SourceTypedPorts Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom LiteralVariableValue

theorem namePortMembership {B : Nat} (Γ : List Ty) (P : PortContext B) {τ : Ty}
    (v : Variable (portTypes P ++ Γ) τ) (p : Fin B) (he : variableName Γ P v=Sum.inl p) : p ∈ P.map Prod.fst := by
  induction P generalizing τ with
  | nil => simp [variableName] at he
  | cons q P ih =>
      cases v with
      | here =>
          simp only [variableName,Sum.inl.injEq] at he
          exact List.mem_cons.mpr (Or.inl he.symm)
      | there v => exact List.mem_cons_of_mem _ (ih v he)

theorem nameInjective : LiteralVariableValueTargets.NameInjective := by
  intro B Γ P
  induction P with
  | nil =>
      intro hd τ v w he
      exact SourceObservationCodingProof.variableIndexInjective v w (Sum.inr.inj he)
  | cons p P ih =>
      intro hd τ v w he
      have hd' := List.nodup_cons.mp hd
      cases v with
      | here =>
          cases w with
          | here => rfl
          | there w => exact False.elim (hd'.1 (namePortMembership Γ P w p.1 he.symm))
      | there v =>
          cases w with
          | here => exact False.elim (hd'.1 (namePortMembership Γ P v p.1 he))
          | there w => exact congrArg Variable.there (ih hd'.2 _ v w he)

theorem freeName {B : Nat} (Γ : List Ty) (P : PortContext B) {τ : Ty} (v : Variable Γ τ) :
    variableName Γ P (shiftVariable (portTypes P) v)=Sum.inr (variableIndex v) := by
  induction P with
  | nil => rfl
  | cons p P ih => exact ih

theorem portName {B : Nat} (Γ : List Ty) (p : Fin B × Ty) (P : PortContext B) (hp : p ∈ P) :
    variableName Γ P (portVariable Γ p P hp)=Sum.inl p.1 := by
  induction P with
  | nil => cases hp
  | cons q P ih =>
      by_cases he : p=q
      · subst q
        simp [portVariable,variableName]
      · simp only [portVariable,dif_neg he,variableName]
        exact ih _

theorem nameExtension : LiteralVariableValueTargets.NameExtension := by
  intro B Γ P Q
  induction P with
  | nil =>
      intro h τ v
      exact freeName Γ Q v
  | cons p P ih =>
      intro h τ v
      cases v with
      | here => exact portName Γ p Q _
      | there v => exact ih _ _ v

theorem literalWeakBits : LiteralVariableValueTargets.LiteralWeakBits := by
  intro Symbol inst arity I τ P v Q o
  simp only [variableRaw,variableBits,decide_eq_true_eq]

theorem availabilityAndStrict : LiteralVariableValueTargets.AvailabilityAndStrict := by
  intro Symbol inst arity I τ P v Q
  exact ⟨rfl,fun _ => rfl⟩

theorem undefinedTables : LiteralVariableValueTargets.UndefinedTables := by
  intro Symbol inst arity I τ P v Q s a
  rfl

theorem naturalVariable : LiteralVariableValueTargets.NaturalVariable := by
  intro Symbol inst arity I τ P v
  constructor
  · intro Q s a b hab; exact le_rfl
  · intro Q R h s a
    exact ExecutableDomainBottomProof.weakeningBottom Symbol inst arity I s.val.2 Q.val R.val h

theorem variableWeakening : LiteralVariableValueTargets.VariableWeakening := by
  intro Symbol inst arity I τ P Q h v
  apply Prod.ext
  · funext R
    simp only [rawWeaken,variableRaw,variableBits,FiniteObservationBits.weaken,
      nameExtension (budget I) I.context P.val Q.val h τ v]
  · rfl

theorem actualValue : LiteralVariableValueTargets.ActualValue := by
  intro Symbol inst arity I τ P v
  refine ⟨layerFold I τ P ⟨variableRaw v,naturalVariable Symbol inst arity I τ P v⟩,?_⟩
  rw [RecursiveNaturalDomainsProof.layerViewFold]

theorem literalVariableEquality : LiteralVariableValueTargets.LiteralVariableEquality := by
  intro Symbol inst arity I τ P v Q o
  rw [literalWeakBits Symbol inst arity I τ P v Q o]
  have hn := nameExtension (budget I) I.context P.val Q.val.val Q.property τ v
  have hd := ((FiniteObservationBitsProof.worldCalibration Symbol arity I Q.val.val).mp Q.val.property).1
  rcases o with ⟨⟨ports,σ,body⟩,ho,hports,hσ⟩
  dsimp at hports hσ ⊢
  subst ports
  subst σ
  cases body <;> simp only [observationName,Option.some.injEq] <;> try simp
  case var w =>
    constructor
    · intro he
      have hw := nameInjective (budget I) I.context Q.val.val hd τ w
        (extendVariables I.context Q.val.val P.val Q.property v) (he.trans hn.symm)
      cases hw
      rfl
    · intro he
      cases he
      exact hn

def variableValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {τ : Ty} {P : World I} (v : Variable (portTypes P.val ++ I.context) τ) : Value I τ P :=
  layerFold I τ P ⟨variableRaw v,naturalVariable Symbol inferInstance arity I τ P v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueProof
