module

public import LogicLineages.PersistentMarking.NumberedWindowScalarProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowExchangeProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramProof
import LogicLineages.PersistentMarking.NumberedWindowLexicalProgramProof
import LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowClassProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowScalarAlgorithm
open NumberedWindowScalarProgramTargets
open NumberedWindowLexicalRequirementPrograms (eqBool)
open List.Vector

abbrev Input := List Nat × Nat × Nat
abbrev Triple := Nat × Nat × Nat

private def readCtx (n : Nat) := ((Encodable.decode n : Option (List Nat)).getD [])
private theorem readPrim : Primrec readCtx := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem admittedPrim (s : Settings) : Primrec (fun p : Input => admitted s p.1 p.2.1 p.2.2) :=
  Primrec.and.comp NumberedWindowLexicalProgramProof.typedPrim
    (Primrec.fst.comp (NumberedWindowAdmissionProgramProof.bitsPrim.comp (Primrec.const s.window)
      (Primrec.snd.comp Primrec.snd)))

private theorem edgePrim (s : Settings) : Primrec (fun p : NumberedWindowClassProgramTargets.ExchangeInput =>
    edge s (readCtx p.1) p.2.1 p.2.2.1 p.2.2.2) := by
  let P := NumberedWindowClassProgramTargets.ExchangeInput
  have ctx : Primrec (fun p : P => readCtx p.1) := readPrim.comp Primrec.fst
  have ty : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have a : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have b : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ex := Primrec.fst.comp (NumberedWindowExchangeProgramProof.bitsPrim.comp
    ((Primrec.const s.equivalentHeads).pair (a.pair b)))
  exact Primrec.and.comp (Primrec.and.comp ex ((admittedPrim s).comp (ctx.pair (ty.pair a))))
    ((admittedPrim s).comp (ctx.pair (ty.pair b)))

private theorem verticesPrim (s : Settings) : Primrec (vertices s) := by
  obtain ⟨p,h⟩ := NumberedWindowCoverBoundsProgramChecks.exact_SelectedCoverProgram
  have row : Primrec (fun n => Encodable.encode s.window.2 ::ᵥ Encodable.encode s.types ::ᵥ n ::ᵥ List.Vector.nil) :=
    Primrec.vector_cons.comp (Primrec.const _) (Primrec.vector_cons.comp (Primrec.const _)
      (Primrec.vector_cons.comp Primrec.id (Primrec.const List.Vector.nil)))
  have covered : Primrec (fun n => NumberedWindowCoverBoundsAlgorithm.cover s.window.2 s.types n) :=
    Primrec.encode_iff.mp (((GorbowPRProgram.Proof.primitiveEvaluation 3 p).comp row).of_eq (h _ _))
  exact Primrec.option_getD.comp covered (Primrec.const [])

private theorem numericLeast (s : Settings) :
    ∃ p : GorbowPRProgram.Program 3, ∀ c t n, GorbowPRProgram.evaluate p (c ::ᵥ t ::ᵥ n ::ᵥ List.Vector.nil) =
      Encodable.encode (least s (readCtx c) t n) :=
  (NumberedWindowClassProgramChecks.exact_ClassPrograms (vertices s) (fun c => edge s (readCtx c))
    (verticesPrim s) (edgePrim s)).2

theorem leastProgram : FixedLeastProgram := by
  intro s
  obtain ⟨p,h⟩ := numericLeast s
  exact ⟨p,fun ctx ty n => by simpa [readCtx] using h (Encodable.encode ctx) ty n⟩

theorem leastPrim (s : Settings) : Primrec (fun p : Input => least s p.1 p.2.1 p.2.2) := by
  obtain ⟨p,h⟩ := leastProgram s
  have args : Primrec (fun i : Input => Encodable.encode i.1 ::ᵥ i.2.1 ::ᵥ i.2.2 ::ᵥ List.Vector.nil) :=
    Primrec.vector_cons.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.vector_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.vector_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const List.Vector.nil)))
  exact Primrec.encode_iff.mp (((GorbowPRProgram.Proof.primitiveEvaluation 3 p).comp args).of_eq
    (fun i => h i.1 i.2.1 i.2.2))

theorem scalarPrim (s : Settings) : Primrec (scalar s) := by
  have canon : Primrec (canonical s) := Primrec.and.comp (admittedPrim s)
    (eqBool.comp (leastPrim s) (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)))
  exact NumberedWindowSyntaxShapePrograms.anyOption NumberedWindowAddressProgramProof.addressPrim
    (canon.comp Primrec.snd).to₂

theorem scalarProgram : FixedScalarProgram := by
  intro s
  apply (GorbowPRProgram.Proof.unaryCorrespondence _).mp
  apply (Primrec.cond (scalarPrim s) (Primrec.const 1) (Primrec.const 0)).of_eq
  intro n
  cases h : scalar s n <;> simp [h]
end LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
