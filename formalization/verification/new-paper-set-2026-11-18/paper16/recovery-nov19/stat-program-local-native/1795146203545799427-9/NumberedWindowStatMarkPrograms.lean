module

public import LogicLineages.PersistentMarking.NumberedWindowStatProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatMarkPrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowStatAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowSyntaxShapePrograms (anyOption)

theorem nodesPrim : Primrec unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

private abbrev Input := Node × Node

private def fits (src argc dst argd : Nat) (p : Input) : Prop :=
  p.1.1 = src ∧ p.1.2.length = argc ∧ p.2.1 = dst ∧ p.2.2.length = argd

private instance (src argc dst argd) (p : Input) : Decidable (fits src argc dst argd p) := by
  unfold fits
  infer_instance

private theorem fitsPrim (src argc dst argd : Nat) : PrimrecPred (fits src argc dst argd) :=
  (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const src)).and
    ((Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const argc)).and
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const dst)).and
        (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const argd))))

private def slot (p : Node) (i : Nat) := p.2.getD i 0

private theorem slotPrim (i : Nat) : Primrec (fun p => slot p i) :=
  (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)

private def lambdaFields (p : Input) : Option Pair :=
  if fits 2 2 2 2 p then
    if slot p.1 0 == slot p.2 0 then some (slot p.1 1,slot p.2 1) else none
  else none

private theorem lambdaFieldsPrim : Primrec lambdaFields :=
  Primrec.ite (fitsPrim 2 2 2 2)
    (Primrec.ite (Primrec.eq.comp (equalPrim.comp ((slotPrim 0).comp Primrec.fst)
      ((slotPrim 0).comp Primrec.snd)) (Primrec.const true))
      (Primrec.option_some.comp (((slotPrim 1).comp Primrec.fst).pair ((slotPrim 1).comp Primrec.snd)))
      (Primrec.const none)) (Primrec.const none)

private theorem peelPartsPrim : Primrec (fun p : Input => peelParts p.1 p.2) := by
  apply lambdaFieldsPrim.of_eq
  rintro ⟨⟨t,xs⟩,⟨u,ys⟩⟩
  unfold lambdaFields
  split
  · rename_i h
    obtain ⟨rfl,hx,rfl,hy⟩ := h
    rw [List.eq_getElem_of_length_eq_two xs hx,List.eq_getElem_of_length_eq_two ys hy]
    rfl
  · unfold peelParts
    split <;> simp_all [fits]

private theorem peelStepPrim : Primrec peelStep := by
  have leftCode := nodesPrim.comp (Primrec.fst : Primrec (Prod.fst : Pair → Nat))
  have rightCode : Primrec (fun p : Pair × Node => unpackNode p.1.2) :=
    nodesPrim.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.option_getD.comp
    (Primrec.option_bind leftCode (Primrec.option_bind rightCode
      (peelPartsPrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂) Primrec.id

private theorem peeled : Primrec (fun p : Pair × Nat => peel p.2 p.1) := by
  have step : Primrec₂ (fun (_ : Pair) (p : Nat × Pair) => peelStep p.2) :=
    peelStepPrim.comp (Primrec.snd.comp Primrec.snd)
  change Primrec₂ (fun p n => peel n p)
  apply (Primrec.nat_rec Primrec.id step).of_eq
  intro p n
  induction n with
  | zero => rfl
  | succ n ih =>
    change peelStep _ = peelStep (peel n p)
    rw [ih]

private def compiled (p : Input) : Bool :=
  if fits 4 2 5 5 p then
    (slot p.1 0 == slot p.2 0) && (slot p.2 1 == (declaration (slot p.1 0)).1) &&
      (slot p.1 1 == slot p.2 3) && (slot p.2 4 == 0)
  else if fits 5 5 5 5 p then
    (slot p.1 0 == slot p.2 0) && (slot p.1 1 == slot p.2 1) &&
      decide (slot p.2 2 < slot p.1 2) &&
      (slot p.1 3 == slot p.2 3) && (slot p.1 4 == slot p.2 4)
  else false

private theorem compiledPrim : Primrec compiled := by
  let x (i : Nat) := (slotPrim i).comp (Primrec.fst : Primrec (Prod.fst : Input → Node))
  let y (i : Nat) := (slotPrim i).comp (Primrec.snd : Primrec (Prod.snd : Input → Node))
  have eq (i : Nat) := equalPrim.comp (x i) (y i)
  have ord := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (eq 0)
    (equalPrim.comp (y 1) (Primrec.fst.comp (NumberedWindowHeadDeclarationPrograms.declarationPrim.comp (x 0)))))
    (equalPrim.comp (x 1) (y 3))) (equalPrim.comp (y 4) (Primrec.const 0))
  have num := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (eq 0) (eq 1))
    (Primrec.nat_lt.comp (y 2) (x 2)).decide) (eq 3)) (eq 4)
  exact Primrec.ite (fitsPrim 4 2 5 5) ord (Primrec.ite (fitsPrim 5 5 5 5) num (Primrec.const false))

private theorem fields5 {xs : List Nat} (h : xs.length = 5) :
    ∃ a b c d e, xs = [a,b,c,d,e] := by
  rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,_ | ⟨f,tail⟩⟩⟩⟩⟩⟩ <;> simp_all

private theorem atomicPrim : Primrec (fun p : Input => atomic p.1 p.2) := by
  apply compiledPrim.of_eq
  rintro ⟨⟨t,xs⟩,⟨u,ys⟩⟩
  unfold compiled
  split
  · rename_i h
    obtain ⟨rfl,hx,rfl,hy⟩ := h
    obtain ⟨a,b,c,d,e,rfl⟩ := fields5 hy
    rw [List.eq_getElem_of_length_eq_two xs hx]
    rfl
  split
  · rename_i h
    obtain ⟨rfl,hx,rfl,hy⟩ := h
    obtain ⟨a,b,c,d,e,rfl⟩ := fields5 hx
    obtain ⟨f,g,k,h,j,rfl⟩ := fields5 hy
    rfl
  · unfold atomic
    split <;> simp_all [fits]

private theorem herePrim : Primrec markHere := by
  have rightCode : Primrec (fun p : Pair × Node => unpackNode p.1.2) :=
    nodesPrim.comp (Primrec.snd.comp Primrec.fst)
  exact anyOption (nodesPrim.comp Primrec.fst)
    (anyOption rightCode (atomicPrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂

theorem markPrim : Primrec₂ mark := by
  have syntaxCheck := Primrec.fst.comp NumberedWindowSyntaxProgramProof.bits
  exact Primrec.and.comp (Primrec.and.comp (syntaxCheck.comp Primrec.fst) (syntaxCheck.comp Primrec.snd))
    (herePrim.comp (peeled.comp (Primrec.id.pair Primrec.fst)))

end LogicLineages.PersistentMarking.NumberedWindowStatMarkPrograms
