module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowCodeConstructors
public import LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
open GorbowSyntax GorbowCodeConstructors

theorem termConstructors : Comparators.GorbowCodeConstructors.TermConstructors := by
  intro n
  exact ⟨fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem formulaConstructors : Comparators.GorbowCodeConstructors.FormulaConstructors := by
  intro n
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

theorem numeralCalibration : Comparators.GorbowCodeConstructors.NumeralCalibration := by
  intro n k
  induction k with
  | zero => rfl
  | succ k ih => simpa [Term.numeral, GorbowTermPrefixCode.encode, numeral, List.replicate_succ] using congrArg (List.cons 2) ih

theorem numericInjection : Comparators.GorbowCodeConstructors.NumericInjection := by
  constructor
  · intro n t u h
    exact GorbowTermPrefixCodeProof.encodingInjective n (Encodable.encode_injective h)
  · intro n φ ψ h
    exact GorbowFormulaPrefixCodeProof.encodingInjective n (Encodable.encode_injective h)

private theorem pr_numeral : Primrec numeral := by
  have hrep : Primrec (fun k : Nat => List.replicate k (2 : Nat)) := by
    have h := Primrec.list_map Primrec.list_range (Primrec.const 2).to₂
    exact h.of_eq (fun k => by simp)
  exact Primrec.list_append.comp hrep (Primrec.const [1])

theorem uniformPrograms : Comparators.GorbowCodeConstructors.UniformPrograms :=
  ⟨Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp Primrec.id (Primrec.const [])),
    Primrec.list_cons,
    Primrec.list_cons.comp Primrec.fst (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)),
    pr_numeral, Primrec.encode⟩

theorem gorbowCodeConstructors : Comparators.GorbowCodeConstructors.Target :=
  ⟨termConstructors, formulaConstructors, numeralCalibration, numericInjection, uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
