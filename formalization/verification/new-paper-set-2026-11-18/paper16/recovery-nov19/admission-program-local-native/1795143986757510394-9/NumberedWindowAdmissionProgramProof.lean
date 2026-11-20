module

public import LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowAdmissionAlgorithm
open NumberedWindowAdmissionProgramTargets NumberedWindowHeadDeclarationPrograms
open NumberedWindowSyntaxShapePrograms (anyOption pairs)

private theorem containsPrim : Primrec₂ (List.contains (α := Nat)) := by
  have mem : PrimrecRel (fun (xs : List Nat) (a : Nat) => a ∈ xs) :=
    (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)).exists_mem_list.of_eq (by simp)
  apply mem.decide.to₂.of_eq
  intro xs a
  apply Bool.eq_iff_iff.mpr
  simp

private theorem termPartsPrim :
    Primrec (fun p : Window × List Row × Nat × List Nat => termParts p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Window × List Row × Nat × List Nat
  have types : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have heads : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have prev : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have tag : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let val (i : Nat) := (Primrec.list_getD (0 : Nat)).comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : P → _))))
    (Primrec.const i)
  let row (i : Nat) := (Primrec.list_getD (false,false)).comp prev (val i)
  let ty (i : Nat) := containsPrim.comp types (val i)
  let hd (i : Nat) := containsPrim.comp heads (val i)
  let tm (i : Nat) := Primrec.fst.comp (row i)
  let ar (i : Nat) := Primrec.snd.comp (row i)
  have bodyTy := Primrec.fst.comp (NumberedWindowAnnotationProgramProof.annotationPrim.comp (val 1))
  have lam := Primrec.and.comp
    (Primrec.and.comp (containsPrim.comp types (arrowPrim.comp (val 0) bodyTy)) (ty 0)) (tm 1)
  have ordinary := Primrec.and.comp (hd 0) (ar 1)
  have numbered := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (hd 0) (ty 1)) (ar 3)) (ar 4)
  have auxiliary := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (ty 1) (ty 0)) (tm 2)) (tm 3)
  apply (choose tag 0 (ty 0) (choose tag 1 (ty 0) (choose tag 2 lam (choose tag 3 (ty 0)
    (choose tag 4 ordinary (choose tag 5 numbered (choose tag 6 auxiliary (Primrec.const false)))))))).of_eq
  rintro ⟨w,prev,tag,fs⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n <;> rfl

private theorem termNextPrim :
    Primrec (fun p : Window × Nat × List Row => termNext p.1 p.2.1 p.2.2) := by
  have node : Primrec NumberedWindowFieldAlgorithm.unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  exact anyOption (node.comp (Primrec.fst.comp Primrec.snd))
    (termPartsPrim.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂

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

private theorem rawBitsPrim : Primrec₂ rawBits := by
  have next : Primrec (fun p : Window × Nat × List Row =>
      (termNext p.1 p.2.1 p.2.2,argsNext p.2.1 p.2.2)) :=
    Primrec.pair termNextPrim (argsNextPrim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have step : Primrec₂ (fun w (p : Nat × List Row) =>
      p.2 ++ [(termNext w p.1 p.2,argsNext p.1 p.2)]) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) (Primrec.list_cons.comp next (Primrec.const []))
  have tables : Primrec₂ table := (Primrec.nat_rec (Primrec.const ([] : List Row)) step).of_eq (fun w n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      change _ ++ [(termNext w n _,argsNext n _)] = _
      simp only [table,← ih])
  exact next.comp (Primrec.fst.pair (Primrec.snd.pair tables))

theorem bitsPrim : Primrec₂ bits := by
  have valid := NumberedWindowSyntaxProgramProof.bits.comp (Primrec.snd : Primrec (Prod.snd : Window × Nat → Nat))
  exact (Primrec.and.comp (Primrec.fst.comp valid) (Primrec.fst.comp rawBitsPrim)).pair
    (Primrec.and.comp (Primrec.snd.comp valid) (Primrec.snd.comp rawBitsPrim))

theorem program : AdmissionProgram := by
  have h : Primrec (fun p : Window × Nat => bits p.1 p.2) :=
    bitsPrim.comp Primrec.fst Primrec.snd
  exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp h)

end LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramProof
