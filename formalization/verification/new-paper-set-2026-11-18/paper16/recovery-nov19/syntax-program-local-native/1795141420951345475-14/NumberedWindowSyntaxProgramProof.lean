module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
open NumberedWindowSyntaxProgramTargets NumberedWindowSyntaxAlgorithm NumberedWindowSyntaxShapePrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowFieldAlgorithm List.Vector

private theorem node : Primrec unpackNode := Primrec.encode_iff.mp
  ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)

private theorem termNextPrim : Primrec₂ termNext :=
  anyOption (node.comp Primrec.fst) (partsPrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂

private theorem argsNextPrim : Primrec₂ argsNext := by
  let check (p : List Row × Nat) := (NumberedWindowPairAlgorithm.decode p.2).any (fun qr =>
    (p.1.getD qr.1 (false,false)).1 && (p.1.getD qr.2 (false,false)).2)
  have prev : Primrec (fun p : (List Row × Nat) × Nat × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have test : Primrec check := anyOption (pairs.comp Primrec.snd) (Primrec.and.comp
    (Primrec.fst.comp ((Primrec.list_getD (false,false)).comp prev (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp ((Primrec.list_getD (false,false)).comp prev (Primrec.snd.comp Primrec.snd)))).to₂
  apply (Primrec.nat_casesOn Primrec.fst (Primrec.const true)
    (test.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
  rintro ⟨n,prev⟩
  cases n <;> rfl

theorem bits : Primrec syntaxBits := by
  have next : Primrec (fun p : Nat × List Row => (termNext p.1 p.2,argsNext p.1 p.2)) := termNextPrim.pair argsNextPrim
  have step : Primrec₂ (fun n (xs : List Row) => xs ++ [(termNext n xs,argsNext n xs)]) :=
    Primrec.list_append.comp Primrec.snd (Primrec.list_cons.comp next (Primrec.const []))
  have tables : Primrec table := (Primrec.nat_rec₁ [] step).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [table,ih])
  exact next.comp (Primrec.id.pair tables)

private theorem program {f : Nat → Bool} (hf : Primrec f) : BooleanProgram f :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp
    ((Primrec.cond hf (Primrec.const 1) (Primrec.const 0)).of_eq (fun n => by cases h : f n <;> simp [h]))

theorem headProgram : NominalHeadProgram := program headPrim
theorem termProgram : RawTermProgram := program (Primrec.fst.comp bits)
theorem argsProgram : RawArgumentProgram := program (Primrec.snd.comp bits)
end LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
