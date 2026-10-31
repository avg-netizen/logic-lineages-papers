module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax
open ForwardTranslation

private theorem collect_codes {α : Type} (n : Nat) (f : Fin n → Option α) (enc : α → Nat) :
    collectAtoms (List.ofFn (fun i => (f i).map enc)) =
      (AdmissibleAssignment.collect n f).map (fun v => List.ofFn (fun i => enc (v i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, collectAtoms, AdmissibleAssignment.collect]
    rw [ih]
    cases hf : f 0 <;> cases hr : AdmissibleAssignment.collect n (fun i => f i.succ) <;> simp

theorem ordinalSyntaxVectorCompilerCorrect : Targets.OrdinalSyntaxVectorCompilerCorrect := by
  intro Γ n v
  unfold vectorCode
  rw [List.ofFn_succ, compileVectorCode]
  have hs := congrArg Prod.snd (ordinalSyntaxExtractionCorrect Γ (v 0))
  have hp : (List.ofFn (fun i : Fin n => typedCode (v i.succ))).map (fun k => (extraction k).1) =
      List.ofFn (fun i => (extractPositive (v i.succ)).map closedPositiveCode) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact congrArg Prod.fst (ordinalSyntaxExtractionCorrect Γ (v i.succ))
  rw [hs, hp, collect_codes]
  unfold compileVector
  cases hscalar : compileScalar (v 0) <;>
    cases hpositive : AdmissibleAssignment.collect n (fun i => extractPositive (v i.succ)) <;>
    simp [CompiledVector.syntaxCode]
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
