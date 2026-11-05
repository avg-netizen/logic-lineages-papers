module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodeSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode.Proof
open OriginalDomain SignedPair FunctionalDetector

private theorem weaken_correct {Γ : List Ty} {τ : Ty} (σ : Ty)
    (a : OriginalTerm Γ τ) : weakenCode (SyntaxCode.encodeTerm a) =
      SyntaxCode.encodeTerm (a.rename (Renaming.weaken Γ σ)) := by
  exact ContextInsertionCode.Proof.exactSourceInsertion [] [σ] Γ τ a

theorem combine_correct {Γ : List Ty} (a b : OriginalTerm Γ unary) :
    combineCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
      SyntaxCode.encodeTerm (combine a b) := by
  unfold combineCode
  rw [weaken_correct (.arrow .ground unary), weaken_correct .ground]
  rfl

theorem project_correct {Γ : List Ty} (a b : OriginalTerm Γ unary) :
    projectCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
      SyntaxCode.encodeTerm (project a b) := by
  unfold projectCode
  rw [weaken_correct unary]
  rfl

theorem omega_correct {Γ : List Ty} (a : OriginalTerm Γ unary) :
    omegaCode (SyntaxCode.encodeTerm a) = SyntaxCode.encodeTerm (liftOmega a) := by
  unfold omegaCode
  rw [weaken_correct .ground]
  rfl

theorem join_correct {Γ : List Ty} (p q : Pair Γ) :
    joinCode (pairCode p) (pairCode q) = pairCode (join p q) := by
  simp only [joinCode, pairCode, join, combine_correct]

private theorem identity_correct (Γ : List Ty) :
    identityCode = SyntaxCode.encodeTerm (@identity Γ) := rfl

theorem eight_correct {Γ : List Ty} (p : Pair Γ) :
    eightCode (pairCode p) = pairCode (timesEight p) := by
  simp only [eightCode, pairCode, identity_correct Γ, timesEight, combine_correct]

theorem sixteen_correct {Γ : List Ty} (p : Pair Γ) :
    sixteenCode (pairCode p) = pairCode (timesSixteen p) := join_correct p p

private theorem iterate_correct {α β : Type*} (code : α → β) (f : α → α) (g : β → β)
    (h : ∀ a, g (code a) = code (f a)) (k : Nat) (a : α) :
    (g^[k]) (code a) = code ((f^[k]) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h]

theorem pad_correct {Γ : List Ty} (d : Nat) (p : Pair Γ) :
    padCode d (pairCode p) = pairCode (pad d p) := by
  unfold padCode SignedPair.pad
  rw [iterate_correct pairCode timesEight eightCode eight_correct,
    iterate_correct pairCode timesSixteen sixteenCode sixteen_correct]

theorem exactCombinators : Targets.ExactCombinators := by
  intro Γ a b p q d
  exact ⟨combine_correct a b, project_correct a b, omega_correct a,
    join_correct p q, pad_correct d p⟩

private theorem leaf_context (Γ Δ : List Ty) (i : Nat) :
    pairCode (@constantLeaf Γ i) = pairCode (@constantLeaf Δ i) := by
  unfold constantLeaf
  split_ifs <;> simp only [pairCode, ← combine_correct, ← project_correct, ← identity_correct]

private theorem balanced_context (Γ Δ : List Ty) (d offset : Nat) :
    pairCode (@balanced Γ d constantLeaf offset) =
      pairCode (@balanced Δ d constantLeaf offset) := by
  induction d generalizing offset with
  | zero => exact leaf_context Γ Δ offset
  | succ d ih =>
      simp only [balanced, ← join_correct, ih]

private theorem unit_correct (Γ : List Ty) : unitCode = pairCode (@unitPair Γ) := by
  exact balanced_context [] Γ 4 0

private theorem higher_lift_code {Γ : List Ty} (a : OriginalTerm Γ OmegaSeed.higherUnary) :
    SyntaxCode.encodeTerm (OmegaSeed.higherLift a) =
      appCode (appCode (8 * SyntaxCode.typeCode unary + 4) 1)
        (lamCode 0 (weakenCode (SyntaxCode.encodeTerm a))) := by
  rw [weaken_correct .ground]
  rfl

private theorem higher_identity_context (Γ Δ : List Ty) :
    SyntaxCode.encodeTerm (@OmegaSeed.higherIdentity Γ) =
      SyntaxCode.encodeTerm (@OmegaSeed.higherIdentity Δ) := rfl

private theorem seed_source_context (Γ Δ : List Ty) :
    SyntaxCode.encodeTerm (@OmegaSeed.source Γ) =
      SyntaxCode.encodeTerm (@OmegaSeed.source Δ) := by
  simp only [OmegaSeed.source, higher_lift_code, higher_identity_context Γ Δ]

private theorem seed_correct (Γ : List Ty) : seedCode = pairCode (@OmegaSeed.pair Γ) := by
  have hu := unit_correct Γ
  change pairCode (@unitPair []) = pairCode (@unitPair Γ) at hu
  have hleft := congrArg Prod.fst hu
  have hright := congrArg Prod.snd hu
  change SyntaxCode.encodeTerm (@unitPair []).1 = SyntaxCode.encodeTerm (@unitPair Γ).1 at hleft
  change SyntaxCode.encodeTerm (@unitPair []).2 = SyntaxCode.encodeTerm (@unitPair Γ).2 at hright
  change (appCode (SyntaxCode.encodeTerm (@OmegaSeed.source []))
      (SyntaxCode.encodeTerm (@unitPair []).1),
    appCode (SyntaxCode.encodeTerm (@OmegaSeed.source []))
      (SyntaxCode.encodeTerm (@unitPair []).2)) =
    (appCode (SyntaxCode.encodeTerm (@OmegaSeed.source Γ))
      (SyntaxCode.encodeTerm (@unitPair Γ).1),
    appCode (SyntaxCode.encodeTerm (@OmegaSeed.source Γ))
      (SyntaxCode.encodeTerm (@unitPair Γ).2))
  rw [seed_source_context [] Γ, hleft, hright]

private theorem input_index : {n : Nat} → (i : Fin n) →
    SourceTypedPorts.variableIndex (inputVariable i) = i.val
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrArg Nat.succ (input_index j)

theorem variable_correct {n : Nat} (i : Fin n) :
    variableCode i.val = pairCode (variablePair i) := by
  have hv : 8 * i.val = SyntaxCode.encodeTerm
      (.var (inputVariable i) : OriginalTerm (Context n) unary) := by
    change 8 * i.val = 8 * SourceTypedPorts.variableIndex (inputVariable i)
    rw [input_index]
  unfold variableCode
  rw [hv, identity_correct (Context n), project_correct, project_correct]
  change joinCode ((eightCode^[3]) (pairCode
    (project (.var (inputVariable i)) identity, project identity identity))) unitCode = _
  rw [iterate_correct pairCode timesEight eightCode eight_correct, unit_correct (Context n),
    join_correct]
  rfl

theorem exactLeaves : Targets.ExactLeaves :=
  ⟨fun Γ => ⟨unit_correct Γ, seed_correct Γ⟩, fun _ i => variable_correct i⟩

private theorem mod_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) % 6 = tag := by omega
private theorem div_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) / 6 = a := by omega

theorem exactCompilerCalibration : Targets.ExactCompilerCalibration := by
  intro n d
  induction d with
  | unit =>
      rw [expressionCode, compilerCode]
      change (unitCode, 12) = (pairCode (@unitPair (Context n)), 12)
      rw [unit_correct (Context n)]
  | var i =>
      rw [expressionCode, compilerCode]
      simp only [mod_tag _ 1 (by decide), div_tag _ 1 (by decide)]
      unfold SeededCompiler.compile
      by_cases hi : i.val < n
      · simp only [hi, ↓reduceDIte, ↓reduceIte]
        rw [variable_correct (⟨i.val, hi⟩ : Fin n)]
      · simp only [hi, ↓reduceDIte, ↓reduceIte]
        rw [seed_correct]
  | add a b iha ihb =>
      rw [expressionCode, compilerCode]
      simp [mod_tag _ 2 (by decide), div_tag _ 2 (by decide), Nat.unpair_pair,
        iha, ihb, addStep, SeededCompiler.compile, pad_correct, join_correct]
  | neg a ih =>
      rw [expressionCode, compilerCode]
      simp [mod_tag _ 3 (by decide), div_tag _ 3 (by decide),
        ih, negStep, SeededCompiler.compile, pairCode]
  | shift a ih =>
      rw [expressionCode, compilerCode]
      simp [mod_tag _ 4 (by decide), div_tag _ 4 (by decide),
        ih, omegaStep, SeededCompiler.compile, pairCode, omega_correct]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode.Proof
