module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowProgramKernelChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowAnnotationAlgorithm List.Vector

theorem arrowPrim : Primrec₂ arrow := by
  have pair : Primrec₂ NumberedWindowPairAlgorithm.pair := by
    obtain ⟨p,h⟩ := NumberedWindowProgramKernelChecks.polynomial
    apply ((GorbowPRProgram.Proof.primitiveEvaluation 2 p).comp
      (Primrec.vector_cons.comp Primrec.fst (Primrec.vector_cons.comp Primrec.snd (Primrec.const List.Vector.nil)))).of_eq
    rintro ⟨a,b⟩
    exact h a b
  exact Primrec.succ.comp pair

theorem choose {α β} [Primcodable α] [Primcodable β] {tag : α → Nat} (ht : Primrec tag)
    (n : Nat) {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if tag a = n then f a else g a) :=
  Primrec.ite (Primrec.eq.comp ht (Primrec.const n)) hf hg

private theorem grounds : Primrec (fun n : Nat => List.replicate n (0 : Nat)) := by
  have step : Primrec₂ (fun (_ : Nat) (l : List Nat) => 0 :: l) := Primrec.list_cons.comp (Primrec.const 0) Primrec.snd
  apply (Primrec.nat_rec₁ ([] : List Nat) step).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.rec_add_one,ih,List.replicate_succ]

private theorem headPartsPrim : Primrec₂ headParts := by
  let P := Nat × Nat
  have tag : Primrec (Prod.fst : P → Nat) := Primrec.fst
  have t : Primrec (Prod.snd : P → Nat) := Primrec.snd
  have tt := arrowPrim.comp t t
  have gtt := arrowPrim.comp (Primrec.const 0) tt
  have c := (arrowPrim.comp (Primrec.const 0) (arrowPrim.comp t tt)).pair (Primrec.const ([] : List Nat))
  have recursor := (arrowPrim.comp (Primrec.const 0) (arrowPrim.comp gtt tt)).pair (Primrec.const ([] : List Nat))
  have p := NumberedWindowSyntaxShapePrograms.pairs.comp t
  have l : Primrec (fun x : P × P => x.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun x : P × P => x.2.2) := Primrec.snd.comp Primrec.snd
  have appDecl := r.pair (Primrec.list_cons.comp (arrowPrim.comp l r)
    (Primrec.list_cons.comp l (Primrec.const [])))
  have rankDecl := (Primrec.const 0).pair (grounds.comp r)
  have app := Primrec.option_getD.comp (Primrec.option_map p appDecl.to₂) (Primrec.const (default : Row))
  have ranked := Primrec.option_getD.comp (Primrec.option_map p rankDecl.to₂) (Primrec.const (default : Row))
  apply (choose tag 0 (Primrec.const (0,[])) (choose tag 1 (Primrec.const (arrow 0 0,[]))
    (choose tag 2 c (choose tag 3 recursor (choose tag 4 app (choose tag 5 ranked (Primrec.const default))))))).of_eq
  rintro ⟨tag,x⟩
  rcases tag with _ | _ | _ | _ | _ | _ | n <;> simp [headParts]
  all_goals cases NumberedWindowPairAlgorithm.decode x <;> rfl

theorem declarationPrim : Primrec declaration :=
  Primrec.option_getD.comp (Primrec.option_map NumberedWindowSyntaxShapePrograms.pairs
    (headPartsPrim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂) (Primrec.const default)

theorem guardOption {α β} [Primcodable α] [Primcodable β] {b : α → Bool} {f : α → β}
    (hb : Primrec b) (hf : Primrec f) : Primrec (fun x => if b x then some (f x) else none) :=
  (Primrec.cond hb (Primrec.option_some.comp hf) (Primrec.const none)).of_eq
    (fun x => by cases h : b x <;> simp [h])

theorem headOutputPrim : Primrec headOutput := guardOption NumberedWindowSyntaxShapePrograms.headPrim declarationPrim

end LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
