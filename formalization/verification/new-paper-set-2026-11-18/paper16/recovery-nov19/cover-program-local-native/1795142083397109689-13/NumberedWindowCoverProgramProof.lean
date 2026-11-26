module

public import LogicLineages.PersistentMarking.NumberedWindowCoverLayerPrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowCoverAlgorithm NumberedWindowCoverProgramTargets
open NumberedWindowCoverLayerPrograms List.Vector

theorem grammarPrim : Primrec₂ (fun (env : Input) depth => grammar env.1 env.2.1 env.2.2 depth) := by
  have recursor := Primrec.nat_rec (Primrec.const (([],[0]) : Layer))
    (layerPrim.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to₂
  apply recursor.of_eq
  intro env n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.rec_add_one, ih, grammar]

private def readList (n : Nat) := ((Encodable.decode n : Option (List Nat)).getD [])
private theorem readListPrim : Primrec readList := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem program : CoverGrammarProgram := by
  let V := List.Vector Nat 4
  have H : Primrec (fun v : V => readList v.head) := readListPrim.comp Primrec.vector_head
  have K := readListPrim.comp (Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail)))
  have tail := Primrec.vector_tail.comp (Primrec.vector_tail : Primrec (fun v : V => v.tail))
  have num := Primrec.vector_head.comp tail
  have depth := Primrec.vector_head.comp (Primrec.vector_tail.comp tail)
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 4 _
    (Primrec.encode.comp (grammarPrim.comp (H.pair (K.pair num)) depth))
  exact ⟨p,fun hs ks n d => by simpa [readList] using eval (Encodable.encode hs ::ᵥ Encodable.encode ks ::ᵥ n ::ᵥ d ::ᵥ List.Vector.nil)⟩
end LogicLineages.PersistentMarking.NumberedWindowCoverProgramProof
