module

public import LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectParsingProof
open LogicLineages.ComputabilityKnowledge NumberedWindowDirectProgramTargets
open NumberedWindowFieldAlgorithm NumberedWindowDirectAlgorithm

theorem fieldsPrim : Primrec unpack := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.2)

private theorem nodePrim : Primrec unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

private def payload (tag : Nat) (p : Nat × List Nat) : Option Entry :=
  if p.1 = tag ∧ p.2.length = 3 then
    some (p.2.getD 0 0, p.2.getD 1 0, p.2.getD 2 0)
  else none

private theorem payloadPrim (tag : Nat) : Primrec (payload tag) := by
  have atSlot (i : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  exact Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.const tag)).and
    (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 3)))
    (Primrec.option_some.comp ((atSlot 0).pair ((atSlot 1).pair (atSlot 2)))) (Primrec.const none)

private theorem payloadMatch (tag t : Nat) (xs : List Nat) : payload tag (t,xs) =
    (if t = tag then match xs with | [a,b,c] => some (a,b,c) | _ => none else none) := by
  by_cases ht : t = tag
  · subst t
    rcases xs with _ | ⟨a,xs⟩
    · simp [payload]
    rcases xs with _ | ⟨b,xs⟩
    · simp [payload]
    rcases xs with _ | ⟨c,xs⟩
    · simp [payload]
    cases xs <;> simp [payload, List.getD_eq_getElem?_getD]
  · simp [payload, ht]

private def three (tag n : Nat) := (unpackNode n).bind (payload tag)
private theorem threePrim (tag : Nat) : Primrec (three tag) :=
  (Primrec.option_bind₁ (payloadPrim tag)).comp nodePrim

private theorem entryPrim : Primrec readEntry := (threePrim 4).of_eq (fun n => by
  unfold three readEntry
  cases unpackNode n with
  | none => rfl
  | some p =>
    rcases p with ⟨t,xs⟩
    simp only [Option.bind_eq_bind, Option.bind_some, payloadMatch]
    by_cases ht : t = 4
    · subst t; simp only [if_pos rfl]; split <;> split <;> grind
    · simp only [if_neg ht]; split <;> grind)

private def both (a : Option α) (b : Option β) : Option (α × β) := do
  let x ← a
  let y ← b
  pure (x,y)

private theorem bothPrim {α β} [Primcodable α] [Primcodable β] [Inhabited α] [Inhabited β] :
    Primrec₂ (@both α β) := by
  apply (Primrec.cond (Primrec.and.comp (Primrec.option_isSome.comp Primrec.fst)
    (Primrec.option_isSome.comp Primrec.snd))
    (Primrec.option_some.comp ((Primrec.option_getD_default.comp Primrec.fst).pair
      (Primrec.option_getD_default.comp Primrec.snd))) (Primrec.const none)).of_eq
  rintro ⟨a,b⟩
  cases a <;> cases b <;> rfl

private def addEntry (n : Nat) (tail : Option (List Entry)) : Option (List Entry) :=
  (both (readEntry n) tail).map (fun p => p.1 :: p.2)

private theorem entriesPrim : Primrec entries := by
  have consPrim : Primrec (fun p : Entry × List Entry => p.1 :: p.2) := Primrec.list_cons
  have addPrim : Primrec₂ addEntry := (Primrec.option_map₁ consPrim).comp
    (bothPrim.comp (entryPrim.comp Primrec.fst) Primrec.snd)
  have foldPrim := Primrec.list_foldr (Primrec.id : Primrec (fun xs : List Nat => xs))
    (Primrec.const (some ([] : List Entry))) (addPrim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply foldPrim.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons n xs ih =>
    change addEntry n (List.foldr addEntry (some []) xs) = _
    rw [ih]
    cases he : readEntry n <;> cases ht : entries xs <;> simp [entries, addEntry, both, he, ht]

private def fromFields (p : Entry) : Option Witness :=
  both (unpack p.1) (both (unpack p.2.1) ((unpack p.2.2).bind entries))

private theorem fromFieldsPrim : Primrec fromFields := bothPrim.comp (fieldsPrim.comp Primrec.fst)
  (bothPrim.comp (fieldsPrim.comp (Primrec.fst.comp Primrec.snd))
    ((Primrec.option_bind₁ entriesPrim).comp (fieldsPrim.comp (Primrec.snd.comp Primrec.snd))))

private theorem witnessPrim : Primrec readWitness := by
  apply ((Primrec.option_bind₁ fromFieldsPrim).comp (threePrim 5)).of_eq
  intro n
  unfold three readWitness
  cases unpackNode n with
  | none => rfl
  | some p =>
    rcases p with ⟨t,xs⟩
    simp only [Option.bind_eq_bind, Option.bind_some, payloadMatch]
    by_cases ht : t = 5
    · subst t
      simp only [if_pos rfl]
      rcases xs with _ | ⟨k,xs⟩
      · rfl
      rcases xs with _ | ⟨r,xs⟩
      · rfl
      rcases xs with _ | ⟨a,xs⟩
      · rfl
      cases xs with
      | cons => rfl
      | nil =>
        simp only [Option.bind_some, fromFields, both]
        cases hk : unpack k <;> cases hr : unpack r <;> cases ha : unpack a <;> simp [hk,hr,ha]
        next es => cases entries es <;> rfl
    · simp only [if_neg ht, Option.bind_none]; split <;> grind

theorem parsing : OccurrenceCertificateParsing := ⟨entryPrim,witnessPrim⟩
end LogicLineages.PersistentMarking.NumberedWindowDirectParsingProof
