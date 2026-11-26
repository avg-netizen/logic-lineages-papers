module

public import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowAnnotationAlgorithm
open NumberedWindowAnnotationProgramTargets NumberedWindowHeadDeclarationPrograms

private theorem termPartsPrim : Primrec (fun p : List Row × Nat × List Nat =>
    termParts p.1 p.2.1 p.2.2) := by
  let P := List Row × Nat × List Nat
  let val (i : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : P → _))) (Primrec.const i)
  have body := Primrec.fst.comp ((Primrec.list_getD (default : Row)).comp Primrec.fst (val 1))
  have tag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  apply (choose tag 0 (val 0) (choose tag 1 (val 0) (choose tag 2 (arrowPrim.comp (val 0) body)
    (choose tag 3 (val 0) (choose tag 4 (Primrec.fst.comp (declarationPrim.comp (val 0)))
    (choose tag 5 (val 1) (choose tag 6 (val 1) (Primrec.const 0)))))))).of_eq
  rintro ⟨t,tag,xs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n <;> simp [termParts]

private theorem termNextPrim : Primrec₂ termNext := by
  have node : Primrec NumberedWindowFieldAlgorithm.unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  exact Primrec.option_getD.comp (Primrec.option_map (node.comp Primrec.fst)
    (termPartsPrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂) (Primrec.const 0)

private theorem argsNextPrim : Primrec₂ argsNext := by
  let check (p : List Row × Nat) := ((NumberedWindowPairAlgorithm.decode p.2).map (fun qr =>
    (p.1.getD qr.1 default).1 :: (p.1.getD qr.2 default).2)).getD []
  have prev : Primrec (fun p : (List Row × Nat) × Nat × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have first := Primrec.fst.comp ((Primrec.list_getD (default : Row)).comp prev (Primrec.fst.comp Primrec.snd))
  have rest := Primrec.snd.comp ((Primrec.list_getD (default : Row)).comp prev (Primrec.snd.comp Primrec.snd))
  have test : Primrec check := Primrec.option_getD.comp
    (Primrec.option_map (NumberedWindowSyntaxShapePrograms.pairs.comp Primrec.snd) (Primrec.list_cons.comp first rest).to₂)
    (Primrec.const [])
  apply (Primrec.nat_casesOn Primrec.fst (Primrec.const ([] : List Nat))
    (test.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
  rintro ⟨n,prev⟩
  cases n <;> rfl

theorem annotationPrim : Primrec annotations := by
  have next : Primrec (fun p : Nat × List Row => (termNext p.1 p.2,argsNext p.1 p.2)) :=
    Primrec.pair termNextPrim argsNextPrim
  have step : Primrec₂ (fun n (xs : List Row) => xs ++ [(termNext n xs,argsNext n xs)]) :=
    Primrec.list_append.comp Primrec.snd (Primrec.list_cons.comp next (Primrec.const []))
  have tables : Primrec table := (Primrec.nat_rec₁ [] step).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [table,ih])
  exact next.comp (Primrec.id.pair tables)

theorem outputPrim : Primrec output := Primrec.pair
  (guardOption (Primrec.fst.comp NumberedWindowSyntaxProgramProof.bits) (Primrec.fst.comp annotationPrim))
  (guardOption (Primrec.snd.comp NumberedWindowSyntaxProgramProof.bits) (Primrec.snd.comp annotationPrim))

theorem declarationProgram : HeadDeclarationProgram :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp headOutputPrim)

theorem annotationProgram : AnnotationProgram :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp outputPrim)
end LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
