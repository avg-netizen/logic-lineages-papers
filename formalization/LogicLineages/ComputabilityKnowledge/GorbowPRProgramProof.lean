module

public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Proof
open List.Vector

theorem primitiveEvaluation : Targets.PrimitiveEvaluation := by
  intro n p
  suffices h : Nat.Primrec' (evaluate p) from h.to_prim
  induction p with
  | zero => exact .zero
  | succ => exact .succ
  | projection i => exact .get i
  | composition f g hf hg => exact .comp (fun i => evaluate (g i)) hf hg
  | recursion f g hf hg => exact .prec hf hg

private theorem programOfTextbook {n : Nat} {f : List.Vector Nat n → Nat}
    (h : Nat.Primrec' f) : ∃ p : Program n, ∀ v, evaluate p v = f v := by
  classical
  induction h with
  | zero => exact ⟨.zero, fun _ => rfl⟩
  | succ => exact ⟨.succ, fun _ => rfl⟩
  | get i => exact ⟨.projection i, fun _ => rfl⟩
  | @comp m n f g hf hg ihf ihg =>
      obtain ⟨p, hp⟩ := ihf
      choose q hq using ihg
      refine ⟨.composition p q, ?_⟩
      intro v
      change evaluate p (ofFn fun i => evaluate (q i) v) = f (ofFn fun i => g i v)
      rw [hp]
      exact congrArg f (congrArg List.Vector.ofFn (funext fun i => hq i v))
  | @prec n f g hf hg ihf ihg =>
      obtain ⟨p, hp⟩ := ihf
      obtain ⟨q, hq⟩ := ihg
      refine ⟨.recursion p q, ?_⟩
      intro v
      simp only [evaluate, hp, hq]

theorem allPrimitiveFunctions : Targets.AllPrimitiveFunctions := by
  intro n f h
  exact programOfTextbook (Nat.Primrec'.of_prim h)

theorem unaryCorrespondence : Targets.UnaryCorrespondence := by
  intro f
  constructor
  · intro h
    obtain ⟨p, hp⟩ := allPrimitiveFunctions 1 (fun v : List.Vector Nat 1 => f v.head)
      (h.comp Primrec.vector_head)
    exact ⟨p, fun x => hp (x ::ᵥ List.Vector.nil)⟩
  · rintro ⟨p, hp⟩
    exact ((primitiveEvaluation 1 p).comp
      (Primrec.vector_cons.comp Primrec.id (.const List.Vector.nil))).of_eq hp

theorem recursionZero : Targets.RecursionZero := by
  intro n f g v
  rfl

theorem recursionSuccessor : Targets.RecursionSuccessor := by
  intro n f g v k
  rfl

end LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Proof
