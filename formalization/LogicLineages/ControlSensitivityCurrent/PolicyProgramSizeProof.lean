module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramSizeTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramObservationProof
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanProof
public import LogicLineages.ControlSensitivityCurrent.PolicyMatrixProof
public import LogicLineages.ControlSensitivityCurrent.PolicyBinaryProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramSize
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open BooleanCompiler ExistentialPlan
open GroundEquivalence PrimitiveLowering

theorem load_bound (Γ : List Ty) (p : Program Γ) :
    p.load ≤ p.codeSize*(p.sourceMax+1) := by
  induction p with
  | matrix d a root => simp [Program.load,Program.codeSize,Program.sourceMax]
  | add a b q ih =>
      simp only [Program.load,Program.codeSize,Program.sourceMax,Nat.add_mul,Nat.one_mul]
      omega
  | literal k q ih =>
      have hb : (Nat.log2 k+2)*1 ≤ (Nat.log2 k+2)*(q.sourceMax+1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [Nat.add_mul,Nat.mul_one] at hb
      simp only [Program.load,Program.codeSize,Program.sourceMax,Nat.add_mul]
      omega
  | observation t q ih =>
      have ht := Nat.le_max_left t.specs.length q.sourceMax
      have hq := Nat.le_max_right t.specs.length q.sourceMax
      have hm : q.codeSize*(q.sourceMax+1) ≤ q.codeSize*(max t.specs.length q.sourceMax+1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [Program.load,Program.codeSize,Program.sourceMax,Nat.add_mul,Nat.one_mul]
      omega
  | unary h x q ih =>
      have ht := Nat.le_max_left h.specs.length q.sourceMax
      have hq := Nat.le_max_right h.specs.length q.sourceMax
      have hm : q.codeSize*(q.sourceMax+1) ≤ q.codeSize*(max h.specs.length q.sourceMax+1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [Program.load,Program.codeSize,Program.sourceMax,Nat.add_mul]
      omega

theorem lower_size (Γ : List Ty) (p : Program Γ) :
    (lower p).vertices ≤ 1000*p.load ∧ (lower p).equations ≤ 1000*p.load ∧
    (lower p).witnesses ≤ 1000*p.load := by
  induction p with
  | @matrix Γ n m d a root =>
      have hb := PolicyMatrix.linearOverhead Γ n m d a root
      simp only [BooleanCompiler.lower,Program.load]
      omega
  | @add Γ a b q ih =>
      simp only [BooleanCompiler.lower,Program.load,ExistentialPlan.Plan.vertices,
        ExistentialPlan.Plan.equations,ExistentialPlan.Plan.witnesses]
      omega
  | @literal Γ k q ih =>
      have hb := PolicyBinary.literalSize Γ k (lower q)
      simp only [BooleanCompiler.lower,Program.load]
      omega
  | @observation Γ t q ih =>
      have hn := (ScopedDAG.Proof.«renaming» Γ (.ground::Γ) .ground
        (Renaming.weaken Γ .ground) t).2
      simp only [BooleanCompiler.lower,Program.load,ExistentialPlan.Plan.vertices,
        ExistentialPlan.Plan.equations,ExistentialPlan.Plan.witnesses,hn]
      change t.specs.length+1+(lower q).vertices ≤ 1000*(t.specs.length+1+q.load) ∧
        1+(lower q).equations ≤ 1000*(t.specs.length+1+q.load) ∧
        1+(lower q).witnesses ≤ 1000*(t.specs.length+1+q.load)
      omega
  | @unary Γ h x q ih =>
      have hn := (ScopedDAG.Proof.«renaming» Γ (.ground::Γ) .ground
        (Renaming.weaken Γ .ground) (call h x)).2
      have hc := (PolicyProgram.observations.2 Γ h x).2
      simp only [BooleanCompiler.lower,Program.load,ExistentialPlan.Plan.vertices,
        ExistentialPlan.Plan.equations,ExistentialPlan.Plan.witnesses,hn,hc]
      change h.specs.length+2+1+(lower q).vertices ≤ 1000*(h.specs.length+3+q.load) ∧
        1+(lower q).equations ≤ 1000*(h.specs.length+3+q.load) ∧
        1+(lower q).witnesses ≤ 1000*(h.specs.length+3+q.load)
      omega
theorem copiedLoad : PolicyProgramSizeTargets.CopiedLoad := load_bound
theorem lowerCounts : PolicyProgramSizeTargets.LowerCounts := lower_size

theorem forestLoadCounts : PolicyProgramSizeTargets.ForestLoadCounts := by
  intro Γ q
  have hs := PolicyPlan.actualSize Γ (lower q)
  have hl := lower_size Γ q
  refine ⟨hs.1.trans hl.1, ?_, ?_⟩
  · rw [hs.2.1]
    exact hl.2.1
  · rw [hs.2.2.1]
    exact Nat.add_le_add_left hl.2.2 Γ.length

theorem forestCodeCounts : PolicyProgramSizeTargets.ForestCodeCounts := by
  intro Γ q
  have hf := forestLoadCounts Γ q
  have hm := Nat.mul_le_mul_left 1000 (load_bound Γ q)
  simp only [← Nat.mul_assoc] at hm
  exact ⟨hf.1.trans hm, hf.2.1.trans hm,
    hf.2.2.trans (Nat.add_le_add_left hm Γ.length)⟩
end LogicLineages.ControlSensitivityCurrent.PolicyProgramSize
