module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowCoverLayerPrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageProgramThinProof
open LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumeric (numbersNumber)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCoverLayerPrograms (Input Layer layerPrim)
open NumberedWindowCoverAlgorithm (applications cells)
open NumberedWindowInternalCoverAuxApplicationsTargets (auxApplications)
open NumberedWindowInternalCoverAuxApplicationsNumericThinProof (exact_AuxApplicationsValue)
open NumberedWindowInternalCoverGrammarStageTargets

theorem sameListCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons a s ih => rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem applicationsPrim : Primrec₂ applications := by
  let X := List Nat × List Nat
  have tape : Primrec (fun p : X => Encodable.encode p.1 ::ᵥ Encodable.encode p.2 ::ᵥ nil) :=
    Primrec.vector_cons.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.vector_cons.comp (Primrec.encode.comp Primrec.snd) (Primrec.const nil))
  have value : Primrec (fun p : X => Encodable.encode (applications p.1 p.2)) := by
    apply ((Proof.primitiveEvaluation 2 auxApplications).comp tape).of_eq
    rintro ⟨K,ts⟩
    rw [sameListCode K,sameListCode ts,sameListCode (applications K ts)]
    exact exact_AuxApplicationsValue K ts
  exact (Primrec.encode_iff.mp value).to₂

private theorem prefixPrim : Primrec (fun p : Input × Layer => originalPrefix p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  let X := Input × Layer
  have all : Primrec (fun p : X => (originalPrefix p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2 ++
      applications p.1.2.1 p.2.1)) := Primrec.fst.comp layerPrim
  have aux : Primrec (fun p : X => applications p.1.2.1 p.2.1) :=
    applicationsPrim.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  let cutoff := Primrec.nat_sub.comp (Primrec.list_length.comp all) (Primrec.list_length.comp aux)
  apply (Primrec.list_take.comp cutoff all).of_eq
  intro p
  rw [List.length_append,Nat.add_sub_cancel]
  simp

private theorem cellsPrim : Primrec₂ cells := by
  let unused : Input := ([],[],0)
  have h : Primrec (fun p : Layer => cells p.1 p.2) :=
    (Primrec.snd.comp layerPrim).comp ((Primrec.const unused).pair Primrec.id)
  exact h.to₂

private def readList (code : Nat) : List Nat := ((Encodable.decode code : Option (List Nat)).getD [])
private theorem readPrim : Primrec readList := Primrec.option_getD.comp Primrec.decode (Primrec.const [])
private theorem readExact (xs : List Nat) : readList (numbersNumber xs) = xs := by
  rw [← sameListCode]
  simp only [readList,Encodable.encodek,Option.getD_some]

private theorem atSlot {n : Nat} (i : Fin n) : Primrec (fun xs : List.Vector Nat n => xs.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

theorem chooseLayerParts : ∃ (nonAux : Program 5) (nextArgs : Program 2), LayerPartsCalibrated nonAux nextArgs := by
  let input := (readPrim.comp (atSlot (0 : Fin 5))).pair
    ((readPrim.comp (atSlot (1 : Fin 5))).pair (atSlot (2 : Fin 5)))
  let previous := (readPrim.comp (atSlot (3 : Fin 5))).pair (readPrim.comp (atSlot (4 : Fin 5)))
  obtain ⟨nonAux,hPrefix⟩ := Proof.allPrimitiveFunctions 5 _ (Primrec.encode.comp (prefixPrim.comp (input.pair previous)))
  obtain ⟨nextArgs,hArgs⟩ := Proof.allPrimitiveFunctions 2 _ (Primrec.encode.comp
    (cellsPrim.comp (readPrim.comp (atSlot (0 : Fin 2))) (readPrim.comp (atSlot (1 : Fin 2)))))
  refine ⟨nonAux,nextArgs,?_,?_⟩
  · intro H K m ts args
    have h := hPrefix (numbersNumber H ::ᵥ numbersNumber K ::ᵥ m ::ᵥ numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil)
    change evaluate nonAux _ = Encodable.encode (originalPrefix (readList (numbersNumber H))
      (readList (numbersNumber K)) m (readList (numbersNumber ts)) (readList (numbersNumber args))) at h
    simpa only [readExact,sameListCode] using h
  · intro ts args
    have h := hArgs (numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil)
    change evaluate nextArgs _ = Encodable.encode (cells (readList (numbersNumber ts)) (readList (numbersNumber args))) at h
    simpa only [readExact,sameListCode] using h

#print axioms chooseLayerParts

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageProgramThinProof
