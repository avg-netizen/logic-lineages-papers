module

public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowRootDispatchAlgorithm List.Vector
open NumberedWindowRootDispatchProgramTargets NumberedWindowRootDispatchStepPrograms
open NumberedWindowSyntaxShapePrograms (anyOption)

theorem checkPrim {rules : Rules} (hr : PrimitiveRules rules) :
    Primrec (fun p : Key => check rules p.1 p.2.1 p.2.2) := by
  have nodes : Primrec NumberedWindowFieldAlgorithm.unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  have source : Primrec (fun p : Key × (Nat × List Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have dest : Primrec (fun p : Key × (Nat × List Nat) => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact anyOption (nodes.comp (Primrec.fst.comp Primrec.snd))
    ((partsPrim hr).comp ((source.pair dest).pair Primrec.snd)).to₂

private theorem indicator (b : Bool) : (if b then 1 else 0) = b.toNat := by cases b <;> rfl

theorem program : RootDispatchProgram := by
  intro rules hr
  have source : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have cert := Primrec.vector_head.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
  have dest := Primrec.vector_head.comp (Primrec.vector_tail.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
  have checkPR := (checkPrim hr).comp (source.pair (cert.pair dest))
  obtain ⟨p,h⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
    (Primrec.ite (Primrec.eq.comp checkPR (Primrec.const true)) (Primrec.const (1 : Nat)) (Primrec.const 0))
  exact ⟨p,fun q w r => (h (q ::ᵥ w ::ᵥ r ::ᵥ List.Vector.nil)).trans (indicator _)⟩

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramProof
