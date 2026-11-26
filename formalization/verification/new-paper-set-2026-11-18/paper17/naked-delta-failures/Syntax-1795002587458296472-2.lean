module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionCollectionProof
public import LogicLineages.PermittedControl.NakedDeltaProgramTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof
@[expose] public section
namespace LogicLineages.PermittedControl.NakedDeltaSyntaxProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open StandardControlCurrent StandardControlCurrent.PolicyAbstractionCollectionProof

def resultVector {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ::Γ) m) (ps : Fin (m+1) → OrdinalPartialVector Γ σ) :
    OrdinalVector Γ (max (σ.level+1) m) :=
  let factor := 2^(σ.level+1)*((List.ofFn h).map ordinalPartialSize).sum
  fun j =>
    
      if j.val=0 then AdmissibleAssignment.repeated p .scalarRepeat factor (ps 0 0)
      else if hj : j.val<σ.level+2 then expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val,hj⟩)
      else ordinalHeadClosure (h ⟨j.val,by have := j.isLt; omega⟩)

theorem coordinate {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ::Γ) m) (ps : Fin (m+1) → OrdinalPartialVector Γ σ)
    (j : Fin (max (σ.level+1) m+1)) :
    NakedDeltaProgram.coordinateCode p σ.level m (vectorCode h)
      (List.ofFn (fun i => List.ofFn (fun k => typedCode (ps i k)))) j.val =
      some (typedCode (resultVector p h ps j)) := by
  have hscalar : ((List.ofFn (fun i => List.ofFn (fun k => typedCode (ps i k)))).getD 0 []).getD 0 0 =
      typedCode (ps 0 0) := by simp [List.getD_eq_getElem?_getD]
  have hp (k : Nat) (hk : k<σ.level+2) :
      PolicyShape.macroCode p (PolicyShape.siteCode .positiveAbstraction) m
        ((List.ofFn (fun i => List.ofFn (fun u => typedCode (ps i u)))).map (fun row => row.getD k 0)) =
        some (typedCode (expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨k,hk⟩))) := by
    have he : (fun i : Fin (m+1) => (List.ofFn (fun u => typedCode (ps i u))).getD k 0) =
        (fun i => typedCode (ps i ⟨k,hk⟩)) := by
      funext i; exact lookup _ ⟨k,hk⟩
    rw [List.map_ofFn]
    dsimp only [Function.comp_def]
    rw [he]
    exact PolicyShapeSyntaxProof.literal.1 p .positiveAbstraction Γ m _
  have hh (k : Nat) (hk : k<m+1) : headClosure ((vectorCode h).getD k 0) =
      typedCode (ordinalHeadClosure (h ⟨k,hk⟩)) := by
    rw [show (vectorCode h).getD k 0=typedCode (h ⟨k,hk⟩) from lookup _ ⟨k,hk⟩]
    exact ordinalSyntaxHeadClosureCorrect Γ σ _
  unfold NakedDeltaProgram.coordinateCode resultVector
  rw [factor Γ σ m h]
  by_cases hz : j.val=0
  · simp only [hz,if_true,dif_pos,hscalar]
    exact PolicyShapeSyntaxProof.literal.2 p .scalarRepeat Γ _ (ps 0 0)
  · simp only [if_neg hz]
    by_cases hl : j.val<σ.level+2
    · simp only [if_pos hl,dif_pos hl]
      exact hp j.val hl
    · have hm : j.val<m+1 := by have := j.isLt; omega
      simp only [if_neg hl,dif_neg hl]
      rw [hh j.val hm]
      rfl

private theorem collect (step : Nat → Option Nat) (out : Nat → Nat)
    (xs : List Nat) (acc : List Nat) (h : ∀ j ∈ xs, step j=some (out j)) :
    xs.foldl (fun acc j => do let ys ← acc; let y ← step j; pure (ys++[y])) (some acc) =
      some (acc ++ xs.map out) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons,h j (by simp),bind,pure,Option.bind_some]
    have hh := ih (acc++[out j]) (fun k hk => h k (by simp [hk]))
    simp only [bind,pure] at hh
    rw [hh]
    simp

theorem result {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ::Γ) m) (ps : Fin (m+1) → OrdinalPartialVector Γ σ) :
    NakedDeltaProgram.resultCode p σ.level m (vectorCode h)
      (List.ofFn (fun i => List.ofFn (fun k => typedCode (ps i k)))) =
      some (vectorCode (resultVector p h ps)) := by
  let out : Nat → Nat := fun j => if hj : j<max (σ.level+1) m+1 then
    typedCode (resultVector p h ps ⟨j,hj⟩) else 0
  unfold NakedDeltaProgram.resultCode
  rw [collect _ out _ []]
  · congr 1
    apply List.ext_getElem
    · simp [vectorCode]
    · intro j hj hk
      have hj' : j<max (σ.level+1) m+1 := by simpa using hj
      simp only [List.nil_append,List.getElem_map,List.getElem_range,vectorCode,List.getElem_ofFn,out,dif_pos hj']
  · intro j hj
    have hj' := List.mem_range.mp hj
    simpa only [out,dif_pos hj'] using coordinate p h ps ⟨j,hj'⟩

theorem literal : NakedDeltaProgramTargets.LiteralCalibration := by
  intro p Γ σ m h
  rw [NakedDeltaProgram.deltaCode,partials p Γ σ m h]
  unfold LiteralCovariance.delta
  cases hc : AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp
  | some ps =>
    simp only [Option.map_some,Option.bind_some,bind,pure]
    exact result p h ps
end LogicLineages.PermittedControl.NakedDeltaSyntaxProof
