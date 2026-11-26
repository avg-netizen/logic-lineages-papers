module
public import LogicLineages.PermittedControl.GroundScalarCircuitCodeTargets
import LogicLineages.PermittedControl.GroundScalarCircuitShapeProof
import LogicLineages.PermittedControl.GroundScalarCircuitSemanticsProof

public section
namespace LogicLineages.PermittedControl.GroundScalarCircuit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.Source.ForwardTranslation (Scalar scalarCode scalarHeadNote)
open OriginalPrintedCircuitSequential (Gate Topological)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate emptyExpression)
open OriginalPrintedRawFamilyFrontend (Args encodeInput)

theorem renameName_node (k j : Nat) : renameName k (nodeName j) = nodeName (k + j) := by
  unfold renameName nodeName
  split_ifs <;> omega

theorem renameName_input (k i : Nat) : renameName k (inputName i) = inputName i := by
  unfold renameName inputName
  split_ifs <;> omega

theorem renameName_zeroName (k : Nat) : renameName k 0 = 0 := rfl

theorem renameName_comp (k j m : Nat) : renameName k (renameName j m) = renameName (k + j) m := by
  unfold renameName
  split_ifs <;> omega

theorem renameName_zero (m : Nat) : renameName 0 m = m := by
  unfold renameName
  split_ifs <;> omega

theorem renameGate_comp (k j : Nat) (g : RawGate) :
    renameGate k (renameGate j g) = renameGate (k + j) g := by
  unfold renameGate
  simp only [List.map_map,Function.comp_def,renameName_comp]

theorem renameGate_zero (g : RawGate) : renameGate 0 g = g := by
  unfold renameGate
  simp [renameName_zero]

theorem renameGates_zero (l : List RawGate) : l.map (renameGate 0) = l := by
  rw [List.map_congr_left (fun g _ => renameGate_zero g),List.map_id']

theorem relCode_one (n : Nat) (h : n % 4 = 0) : relCode n = [leafGate (1,[])] := by
  conv_lhs => rw [relCode]
  simp [h]

theorem relCode_var (i : Nat) : relCode (4 * i + 1) = [leafGate (1,[(1,inputName i)])] := by
  conv_lhs => rw [relCode]
  have h1 : (4 * i + 1) % 4 = 1 := by omega
  have h2 : (4 * i + 1) / 4 = i := by omega
  simp [h1,h2]

theorem relCode_add (x y : Nat) :
    relCode (4 * Nat.pair x y + 2) =
      relCode x ++ (relCode y).map (renameGate (relCode x).length) ++
        [addGate (relCode x).length (relCode y).length] := by
  conv_lhs => rw [relCode]
  have h1 : (4 * Nat.pair x y + 2) % 4 = 2 := by omega
  have h2 : (4 * Nat.pair x y + 2) / 4 = Nat.pair x y := by omega
  simp [h1,h2,Nat.unpair_pair]

theorem relCode_shift (x y : Nat) :
    relCode (4 * Nat.pair x y + 3) = relCode y ++ [shiftGate x (relCode y).length] := by
  conv_lhs => rw [relCode]
  have h1 : (4 * Nat.pair x y + 3) % 4 = 3 := by omega
  have h2 : (4 * Nat.pair x y + 3) / 4 = Nat.pair x y := by omega
  simp [h1,h2,Nat.unpair_pair]

theorem circuitCalibration : CircuitCalibration := by
  intro ι index s
  induction s with
  | one =>
    intro k
    have hc : scalarCode index (Scalar.one : Scalar ι) = 4 := rfl
    rw [hc,relCode_one 4 (by decide)]
    refine ⟨?_,?_,?_,?_⟩
    · show [encodeGate (.base (.affine (1,[]) (nodeName k)))] = [renameGate k (leafGate (1,[]))]
      simp [encodeGate,renameGate,leafGate,renameName_node,renameName_zeroName]
    · show k + 1 = k + 1
      rfl
    · show nodeName k = nodeName (k + 1 - 1)
      rfl
    · show 0 < 1
      decide
  | var x =>
    intro k
    have hc : scalarCode index (Scalar.var x) = 4 * index x + 1 := rfl
    rw [hc,relCode_var]
    refine ⟨?_,?_,?_,?_⟩
    · show [encodeGate (.base (.affine (1,[(1,inputName (index x))]) (nodeName k)))] =
        [renameGate k (leafGate (1,[(1,inputName (index x))]))]
      simp [encodeGate,renameGate,leafGate,renameName_node,renameName_zeroName,renameName_input]
    · show k + 1 = k + 1
      rfl
    · show nodeName k = nodeName (k + 1 - 1)
      rfl
    · show 0 < 1
      decide
  | add a b iha ihb =>
    intro k
    obtain ⟨ga,na,oa,pa⟩ := iha k
    obtain ⟨gb,nb,ob,pb⟩ := ihb (circuitOf index a k).2.2
    have hc : scalarCode index (Scalar.add a b) =
        4 * Nat.pair (scalarCode index a) (scalarCode index b) + 2 := rfl
    rw [hc,relCode_add,circuitOf_add]
    generalize circuitOf index a k = A at *
    generalize circuitOf index b A.2.2 = B at *
    generalize relCode (scalarCode index a) = RA at *
    generalize relCode (scalarCode index b) = RB at *
    dsimp only
    refine ⟨?_,?_,?_,?_⟩
    · rw [List.map_append,List.map_append,ga,gb,List.map_append,List.map_append,List.map_map,na]
      have mid : RB.map (renameGate (k + RA.length)) = RB.map (renameGate k ∘ renameGate RA.length) :=
        List.map_congr_left (fun g _ => (renameGate_comp k RA.length g).symm)
      rw [mid]
      congr 1
      show [((0 : Nat),(0 : Nat),nodeName B.2.2,((0 : Nat),(0 : Nat)),((0 : Int),[((1 : Int),A.2.1),((1 : Int),B.2.1)]))] =
        [renameGate k (addGate RA.length RB.length)]
      rw [oa,ob,nb,na]
      simp only [renameGate,addGate,renameName_node,renameName_zeroName,List.map_cons,List.map_nil]
      rw [show k + RA.length + RB.length - 1 = k + (RA.length + RB.length - 1) by omega,
        show k + RA.length - 1 = k + (RA.length - 1) by omega,
        show k + RA.length + RB.length = k + (RA.length + RB.length) by omega]
    · simp only [List.length_append,List.length_map,List.length_singleton]
      omega
    · simp only [List.length_append,List.length_map,List.length_singleton]
      rw [nb,na]
      congr 1
      omega
    · simp only [List.length_append,List.length_map,List.length_singleton]
      omega
  | shift c a iha =>
    intro k
    obtain ⟨ga,na,oa,pa⟩ := iha k
    have hc : scalarCode index (Scalar.shift c a) =
        4 * Nat.pair (OrdinalComparison.rawNoteEncode (scalarHeadNote c).1) (scalarCode index a) + 3 := rfl
    rw [hc,relCode_shift,circuitOf_shift]
    generalize circuitOf index a k = A at *
    generalize relCode (scalarCode index a) = RA at *
    dsimp only
    refine ⟨?_,?_,?_,?_⟩
    · rw [List.map_append,ga,List.map_append]
      congr 1
      show [((1 : Nat),A.2.1,nodeName A.2.2,(OrdinalComparison.rawNoteEncode (scalarHeadNote c).1,(0 : Nat)),
          emptyExpression)] =
        [renameGate k (shiftGate (OrdinalComparison.rawNoteEncode (scalarHeadNote c).1) RA.length)]
      rw [oa,na]
      simp only [renameGate,shiftGate,renameName_node,emptyExpression,List.map_nil]
      rw [show k + RA.length - 1 = k + (RA.length - 1) by omega]
    · simp only [List.length_append,List.length_singleton]
      omega
    · simp only [List.length_append,List.length_singleton]
      rw [na,show k + (RA.length + 1) - 1 = k + RA.length by omega]
    · simp only [List.length_append,List.length_singleton]
      try omega

theorem counterCodeEq (tag a b : Nat) : counterCode tag a b = (counterFormula tag a b).encode := by
  unfold counterCode counterFormula
  split_ifs <;> rfl

theorem exactQueryCode : ExactQueryCode := by
  intro tag ι index sa sb
  refine ⟨(block index tag sa sb).known,(block index tag sa sb).gates,(block index tag sa sb).matrix,
    (blockShape ι index tag sa sb).1,(blockShape ι index tag sa sb).2,?_,
    fun f B hf => blockCorrect f B hf ι index tag sa sb⟩
  obtain ⟨ga,na,oa,_⟩ := circuitCalibration index sa 0
  obtain ⟨gb,_,ob,_⟩ := circuitCalibration index sb (circuitOf index sa 0).2.2
  show queryCode tag (scalarCode index sa) (scalarCode index sb) =
    (((List.range (scalarCode index sa + scalarCode index sb + 1)).map inputName,
      (counterFormula tag (circuitOf index sa 0).2.1 (circuitOf index sb (circuitOf index sa 0).2.2).2.1).encode,
      ((circuitOf index sa 0).1 ++ (circuitOf index sb (circuitOf index sa 0).2.2).1).map encodeGate),true)
  rw [List.map_append,ga,gb,← counterCodeEq,ob,oa,na,renameGates_zero]
  simp only [Nat.zero_add]
  rfl

#print axioms circuitCalibration
#print axioms exactQueryCode

end LogicLineages.PermittedControl.GroundScalarCircuit
