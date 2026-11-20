module
public import LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramTargets
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
public section
namespace LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowTypedProbe NumberedWindowTypedProbeProgramTargets NumberedWindowScalarAlgorithm
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowFreeAddress (freeAddress freshName)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowScalarProgramProof (scalarPrim)
open NumberedWindowSyntaxShapePrograms (anyOption pairs)
private theorem typedPrim (s : Settings) : Primrec₂ (typed s) := by
  let X := Nat × Nat
  have ty : Primrec (fun row : X × Address => row.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.and.comp ((scalarPrim s).comp Primrec.snd)
    (anyOption (addressPrim.comp Primrec.snd) (equalPrim.comp ty (Primrec.fst.comp Primrec.fst)).to₂)).to₂

private theorem makeFree : Primrec (fun row : List Nat × Nat × Nat => freeAddress row.1 row.2.1 row.2.2) := by
  obtain ⟨p,h⟩ := NumberedWindowFreeAddressProgramChecks.exact_FreeAddressPrograms.1
  apply ((Proof.primitiveEvaluation 3 p).comp (Primrec.vector_cons.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.vector_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.vector_cons.comp
      (Primrec.snd.comp Primrec.snd) (Primrec.const nil))))).of_eq
  exact fun x => h x.1 x.2.1 x.2.2

private theorem probePrim (s : Settings) : Primrec (probe s) := by
  have arrow : Primrec arrowView := (Primrec.nat_casesOn₁ none pairs).of_eq (fun n => by cases n <;> rfl)
  have fresh : Primrec freshName := (Proof.unaryCorrespondence _).mpr
    NumberedWindowFreeAddressProgramChecks.exact_FreeAddressPrograms.2
  let X := Address × Nat × Nat
  have context : Primrec (fun row : X => row.1.1) := Primrec.fst.comp Primrec.fst
  have dom : Primrec (fun row : X => row.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun row : X => freshName row.1.2.2) :=
    fresh.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have fn : Primrec (fun a : Address => (arrowView a.2.1).map
      (fun pair => freeAddress a.1 pair.1 (freshName a.2.2))) :=
    Primrec.option_map (arrow.comp (Primrec.fst.comp Primrec.snd))
      (makeFree.comp (context.pair (dom.pair n))).to₂
  apply (Primrec.ite (Primrec.eq.comp (scalarPrim s) (Primrec.const true))
    ((Primrec.option_bind₁ fn).comp addressPrim) (Primrec.const none)).of_eq
  intro n
  unfold probe
  split
  · simp only [Option.bind_eq_bind]
    congr 1
    funext a
    cases arrowView a.2.1 <;> rfl
  · rfl

theorem exact_TypedProbePrograms : TypedProbePrograms := by
  intro s
  constructor
  · have t : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
    have n := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 2 => v.tail))
    have pred := (typedPrim s).comp t n
    obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 2 _
      (Primrec.cond pred (Primrec.const (1 : Nat)) (Primrec.const 0))
    refine ⟨p,fun t n => (h (t ::ᵥ n ::ᵥ nil)).trans ?_⟩
    change (if typed s t n then 1 else 0) = (typed s t n).toNat
    cases typed s t n <;> rfl
  · exact (Proof.unaryCorrespondence _).mp (Primrec.encode.comp (probePrim s))
#print axioms exact_TypedProbePrograms
end LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramChecks
