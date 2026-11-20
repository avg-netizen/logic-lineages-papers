module

public import LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowLexicalProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowLexicalAlgorithm
open NumberedWindowLexicalProgramTargets NumberedWindowLexicalRequirementPrograms
open NumberedWindowHeadDeclarationPrograms (choose arrowPrim declarationPrim)
open NumberedWindowAnnotationProgramProof (annotationPrim)
open List.Vector

private theorem partsPrim : Primrec (fun p : List Row × Nat × List Nat =>
    termParts p.1 p.2.1 p.2.2) := by
  let P := List Row × Nat × List Nat
  let val (i : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : P → _))) (Primrec.const i)
  let entry (i : Nat) := (Primrec.list_getD (default : Row)).comp Primrec.fst (val i)
  let tm (i : Nat) := Primrec.fst.comp (entry i)
  let ar (i : Nat) := Primrec.snd.comp (entry i)
  let ann (i : Nat) := annotationPrim.comp (val i)
  let argsMatch (i : Nat) := eqBool.comp (Primrec.snd.comp (ann i)) (Primrec.snd.comp (declarationPrim.comp (val 0)))
  have tag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have fnOk := eqBool.comp (Primrec.fst.comp (ann 2)) (arrowPrim.comp (val 0) (val 1))
  have argOk := eqBool.comp (Primrec.fst.comp (ann 3)) (val 0)
  have app := joinPrim.comp (restrictPrim.comp fnOk (tm 2)) (restrictPrim.comp argOk (tm 3))
  have ord := restrictPrim.comp (argsMatch 1) (ar 1)
  have num := restrictPrim.comp (argsMatch 3) (joinPrim.comp (ar 3) (ar 4))
  apply (choose tag 0 (Primrec.const empty) (choose tag 1 (slotPrim.comp (val 1) (val 0))
    (choose tag 2 (binderPrim.comp (val 0) (tm 1)) (choose tag 3 (Primrec.const empty)
    (choose tag 4 ord (choose tag 5 num (choose tag 6 app (Primrec.const default)))))))).of_eq
  rintro ⟨t,tag,xs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n <;> simp [termParts]

private theorem termNextPrim : Primrec₂ termNext := by
  have node : Primrec NumberedWindowFieldAlgorithm.unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  exact Primrec.option_getD.comp (Primrec.option_map (node.comp Primrec.fst)
    (partsPrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂) (Primrec.const default)

private theorem argsNextPrim : Primrec₂ argsNext := by
  let check (p : List Row × Nat) := ((NumberedWindowPairAlgorithm.decode p.2).map (fun qr =>
    join (p.1.getD qr.1 default).1 (p.1.getD qr.2 default).2)).getD default
  have prev : Primrec (fun p : (List Row × Nat) × Nat × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have first := Primrec.fst.comp ((Primrec.list_getD (default : Row)).comp prev (Primrec.fst.comp Primrec.snd))
  have rest := Primrec.snd.comp ((Primrec.list_getD (default : Row)).comp prev (Primrec.snd.comp Primrec.snd))
  have test : Primrec check := Primrec.option_getD.comp
    (Primrec.option_map (NumberedWindowSyntaxShapePrograms.pairs.comp Primrec.snd) (joinPrim.comp first rest).to₂)
    (Primrec.const default)
  apply (Primrec.nat_casesOn Primrec.fst (Primrec.const empty)
    (test.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
  rintro ⟨n,prev⟩
  cases n <;> rfl

theorem reqPrim : Primrec requirements := by
  have next : Primrec (fun p : Nat × List Row => (termNext p.1 p.2,argsNext p.1 p.2)) :=
    Primrec.pair termNextPrim argsNextPrim
  have step : Primrec₂ (fun n (xs : List Row) => xs ++ [(termNext n xs,argsNext n xs)]) :=
    Primrec.list_append.comp Primrec.snd (Primrec.list_cons.comp next (Primrec.const []))
  have tables : Primrec table := (Primrec.nat_rec₁ [] step).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [table,ih])
  exact next.comp (Primrec.id.pair tables)

theorem typedPrim : Primrec (fun p : List Nat × Nat × Nat => typed p.1 p.2.1 p.2.2) := by
  let P := List Nat × Nat × Nat
  have seed : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have ty : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have synt := Primrec.fst.comp (NumberedWindowSyntaxProgramProof.bits.comp seed)
  have same := eqBool.comp (Primrec.fst.comp (annotationPrim.comp seed)) ty
  exact Primrec.and.comp (Primrec.and.comp synt same)
    (holdsPrim.comp Primrec.fst (Primrec.fst.comp (reqPrim.comp seed)))

theorem requirementsProgram : RequirementsProgram :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp reqPrim)

private def readCtx (n : Nat) := ((Encodable.decode n : Option (List Nat)).getD [])

theorem finiteTypedProgram : FiniteTypedProgram := by
  let V := List.Vector Nat 3
  have read : Primrec readCtx := Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have ty := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail))
  have n := Primrec.vector_head.comp (Primrec.vector_tail.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail)))
  have bit := typedPrim.comp ((read.comp Primrec.vector_head).pair (ty.pair n))
  have result : Primrec (fun v : V => if typed (readCtx v.head) v.tail.head v.tail.tail.head then 1 else 0) := by
    apply (Primrec.cond bit (Primrec.const 1) (Primrec.const 0)).of_eq
    intro v
    cases h : typed (readCtx v.head) v.tail.head v.tail.tail.head <;> simp [h]
  obtain ⟨p,e⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ result
  exact ⟨p,fun ctx t n => by simpa [readCtx] using e (Encodable.encode ctx ::ᵥ t ::ᵥ n ::ᵥ List.Vector.nil)⟩
end LogicLineages.PersistentMarking.NumberedWindowLexicalProgramProof
