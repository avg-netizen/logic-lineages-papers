module
public import LogicLineages.OrdinalComparison.SourceBooleanWireTargets
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanWire.Proof

theorem nodeExact : Targets.NodeExact := by
  intro n m a w g b z
  cases g with
  | eq x y =>
      constructor
      · intro h
        simp [LocalHolds,constraints,Atom.Holds,Ref.value] at h
        have hb : b = bit (evalNode a w (.eq x y)) := by
          by_cases he : a x = a y <;> simp [evalNode,bit,he] <;> omega
        refine ⟨hb,?_⟩
        funext i
        fin_cases i <;> simp [canonicalAux] <;> omega
      · rintro ⟨rfl,rfl⟩
        by_cases he : a x = a y <;>
          simp [LocalHolds,constraints,Atom.Holds,Ref.value,canonicalAux,evalNode,bit,he] <;> omega
  | le x y =>
      constructor
      · intro h
        simp [LocalHolds,constraints,Atom.Holds,Ref.value] at h
        have hb : b = bit (evalNode a w (.le x y)) := by
          by_cases he : a x ≤ a y <;> simp [evalNode,bit,he] <;> omega
        refine ⟨hb,?_⟩
        funext i
        fin_cases i <;> simp [canonicalAux] <;> omega
      · rintro ⟨rfl,rfl⟩
        by_cases he : a x ≤ a y <;>
          simp [LocalHolds,constraints,Atom.Holds,Ref.value,canonicalAux,evalNode,bit,he] <;> omega
  | lt x y =>
      constructor
      · intro h
        simp [LocalHolds,constraints,Atom.Holds,Ref.value] at h
        have hb : b = bit (evalNode a w (.lt x y)) := by
          by_cases he : a x < a y <;> simp [evalNode,bit,he] <;> omega
        refine ⟨hb,?_⟩
        funext i
        fin_cases i <;> simp [canonicalAux] <;> omega
      · rintro ⟨rfl,rfl⟩
        by_cases he : a x < a y <;>
          simp [LocalHolds,constraints,Atom.Holds,Ref.value,canonicalAux,evalNode,bit,he] <;> omega
  | neg c =>
      constructor
      · intro h
        simp [LocalHolds,constraints,zeroAux,Atom.Holds,Ref.value] at h
        have hb : b = bit (evalNode a w (.neg c)) := by
          cases hc : w c <;> simp [evalNode,bit,hc] at * <;> omega
        refine ⟨hb,?_⟩
        funext i
        fin_cases i <;> simp [canonicalAux] <;> omega
      · rintro ⟨rfl,rfl⟩
        cases hc : w c <;>
          simp [LocalHolds,constraints,zeroAux,Atom.Holds,Ref.value,canonicalAux,evalNode,bit,hc]
        all_goals intro i; fin_cases i <;> rfl
  | conj c d =>
      constructor
      · intro h
        simp [LocalHolds,constraints,Atom.Holds,Ref.value] at h
        have hb : b = bit (evalNode a w (.conj c d)) := by
          cases hc : w c <;> cases hd : w d <;> simp [evalNode,bit,hc,hd] at * <;> omega
        refine ⟨hb,?_⟩
        funext i
        fin_cases i <;> simp [canonicalAux] <;> omega
      · rintro ⟨rfl,rfl⟩
        cases hc : w c <;> cases hd : w d <;>
          simp [LocalHolds,constraints,Atom.Holds,Ref.value,canonicalAux,evalNode,bit,hc,hd]
  | disj c d =>
      constructor
      · intro h
        simp [LocalHolds,constraints,Atom.Holds,Ref.value] at h
        have hb : b = bit (evalNode a w (.disj c d)) := by
          cases hc : w c <;> cases hd : w d <;> simp [evalNode,bit,hc,hd] at * <;> omega
        refine ⟨hb,?_⟩
        funext i
        fin_cases i <;> simp [canonicalAux] <;> omega
      · rintro ⟨rfl,rfl⟩
        cases hc : w c <;> cases hd : w d <;>
          simp [LocalHolds,constraints,Atom.Holds,Ref.value,canonicalAux,evalNode,bit,hc,hd]

theorem wireExact : Targets.WireExact := by
  intro n m d a w z
  induction d with
  | nil =>
      constructor
      · intro _
        constructor <;> funext i <;> exact Fin.elim0 i
      · intro _; trivial
  | @snoc m d g ih =>
      constructor
      · intro h
        have ht := (ih (fun i => w i.succ) (fun i => z i.succ)).mp h.1
        have hn := h.2
        rw [ht.1] at hn
        have hg := (nodeExact n m a (evaluate d a) g (w 0) (z 0)).mp hn
        constructor
        · funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact hg.1
          · exact congrFun ht.1 j
        · funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact hg.2
          · exact congrFun ht.2 j
      · rintro ⟨rfl,rfl⟩
        constructor
        · exact (ih _ _).mpr ⟨rfl,rfl⟩
        · exact (nodeExact n m a (evaluate d a) g _ _).mpr ⟨rfl,rfl⟩

theorem uniqueWitnesses : Targets.UniqueWitnesses := by
  intro n m d a
  refine ⟨⟨fun i => bit (evaluate d a i),witnesses d a⟩,?_,?_⟩
  · exact (wireExact n m d a _ _).mpr ⟨rfl,rfl⟩
  · intro p hp
    obtain ⟨hw,hz⟩ := (wireExact n m d a p.1 p.2).mp hp
    exact Prod.ext hw hz

theorem rootCorrect : Targets.RootCorrect := by
  intro n m d a root
  constructor
  · rintro ⟨w,z,hw,hr⟩
    obtain ⟨rfl,rfl⟩ := (wireExact n m d a w z).mp hw
    cases he : evaluate d a root <;> simp [bit,he] at hr ⊢
  · intro hr
    refine ⟨(fun i => bit (evaluate d a i)),witnesses d a,?_,?_⟩
    · exact (wireExact n m d a _ _).mpr ⟨rfl,rfl⟩
    · simp [hr,bit]

theorem node_bound (n m : Nat) (g : Node n m) : (constraints g).length ≤ 9 := by
  cases g <;> simp [constraints,zeroAux]

theorem linearOverhead : Targets.LinearOverhead := by
  refine ⟨node_bound,?_⟩
  intro n m d
  induction d with
  | nil => simp [atomCount,newWireCount]
  | @snoc m d g ih =>
      have hg := node_bound n m g
      simp only [atomCount,newWireCount]
      constructor <;> omega
end LogicLineages.OrdinalComparison.Source.BooleanWire.Proof
