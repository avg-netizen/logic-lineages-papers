module

public import LogicLineages.PersistentMarking.NumberedWindowStatPartitionPrograms
import LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowStatAlgorithm List.Vector
open NumberedWindowStatProgramTargets NumberedWindowStatMarkPrograms NumberedWindowStatPartitionPrograms
open NumberedWindowSyntaxShapePrograms (anyOption)

private theorem permPrim : Primrec₂ (fun (xs ys : List Nat) => decide (xs.Perm ys)) := by
  let accept (_ : Nat) := true
  let reject (_ _ _ : Nat) := false
  have direct := NumberedWindowDirectListsPrimrec.directListsPrimitive accept reject
    (Primrec.const true) (Primrec.const false)
  let W := NumberedWindowDirectAlgorithm.Witness
  have witness : Primrec (fun p : List Nat × List Nat => ((p.2,[0],[]) : W)) :=
    Primrec.snd.pair (Primrec.const ([0],[]))
  have source := Primrec.list_append.comp (Primrec.fst : Primrec (Prod.fst : List Nat × List Nat → List Nat)) (Primrec.const [0])
  apply ((direct.comp (source.pair (Primrec.snd.pair witness))).to₂).of_eq
  intro xs ys
  apply Bool.eq_iff_iff.mpr
  simp [NumberedWindowDirectAlgorithm.directLists,accept,List.perm_append_right_iff]

private theorem anyRemoved : Primrec₂ (fun (xs : List Nat) (target : Nat) =>
    xs.any (fun src => mark src target)) := by
  have test : PrimrecRel (fun src target => mark src target = true) :=
    Primrec.eq.comp markPrim (Primrec.const true)
  apply test.exists_mem_list.decide.to₂.of_eq
  intro xs target
  apply Bool.eq_iff_iff.mpr
  simp

private theorem listsPrim : Primrec
    (fun p : List Nat × List Nat × Partition => replacementLists p.1 p.2.1 p.2.2) := by
  let P := List Nat × List Nat × Partition
  have q : Primrec (fun p : P => p.1) := Primrec.fst
  have r : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have parts : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have kept := Primrec.fst.comp parts
  have removed := Primrec.fst.comp (Primrec.snd.comp parts)
  have added := Primrec.snd.comp (Primrec.snd.comp parts)
  have sourcePerm := permPrim.comp q (Primrec.list_append.comp kept removed)
  have targetPerm := permPrim.comp r (Primrec.list_append.comp kept added)
  have nonempty : Primrec (fun p : P => !p.2.2.2.1.isEmpty) :=
    ((Primrec.eq.comp removed (Primrec.const ([] : List Nat))).not.decide).of_eq
      (fun p => by cases p.2.2.2.1 <;> simp)
  have everyInserted :=
    (NumberedWindowDirectListsPrimrec.allWith
      (anyRemoved.comp Primrec.snd Primrec.fst).to₂).comp added removed
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp sourcePerm targetPerm) nonempty) everyInserted

abbrev Inputs := Nat × Nat × Nat

theorem replacementPrim : Primrec (fun p : Inputs => replacement p.1 p.2.1 p.2.2) := by
  let A := Inputs × List Nat
  let B := A × Partition
  let C := B × List Nat
  have source := argsViewPrim.comp (Primrec.fst : Primrec (Prod.fst : Inputs → Nat))
  have cert : Primrec (fun p : A => readPartition p.1.2.1) :=
    partitionPrim.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have target : Primrec (fun p : B => argsView p.1.1.2.2) :=
    argsViewPrim.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have selectArgs : Primrec (fun p : C => (p.1.1.2,p.2,p.1.2)) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))
  apply (anyOption source (anyOption cert (anyOption target (listsPrim.comp selectArgs).to₂).to₂).to₂).of_eq
  rintro ⟨q,w,r⟩
  cases hq : argsView q <;> cases hw : readPartition w <;> cases hr : argsView r <;>
    simp [replacement,hq,hw,hr,Option.any]

private theorem indicator {α} [Primcodable α] {f : α → Bool} (h : Primrec f) :
    Primrec (fun x => if f x then 1 else 0) :=
  Primrec.ite (Primrec.eq.comp h (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)

theorem programs : StatPrograms := by
  constructor
  · have q : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
    have r := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 2 => v.tail))
    have h : Primrec (fun v : List.Vector Nat 2 => mark v.head v.tail.head) := markPrim.comp q r
    obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ (indicator h)
    exact ⟨p,fun q r => eval (q ::ᵥ r ::ᵥ List.Vector.nil)⟩
  · have q : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
    have w := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
    have r := Primrec.vector_head.comp (Primrec.vector_tail.comp
      (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
    obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
      (indicator (replacementPrim.comp (q.pair (w.pair r))))
    exact ⟨p,fun q w r => eval (q ::ᵥ w ::ᵥ r ::ᵥ List.Vector.nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowStatProgramProof
