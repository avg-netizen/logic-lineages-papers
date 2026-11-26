module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLowTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLowUnifiedProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalPrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsDataProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericPlainTerminal (boolCode boolCodePrimitive)

private theorem pointComputable (f : Nat → Nat) (hf : Computable f) :
    Computable₂ (lowPoint f) := by
  let P := LowArgs × Nat
  have rank : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have remain : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have data : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp remain
  have values : Primrec (fun p : P => p.1.2.2.1) := Primrec.fst.comp data
  have rest : Primrec (fun p : P => p.1.2.2.2) := Primrec.snd.comp data
  have inst := Primrec.list_set.comp values (rank.pair Primrec.snd)
  have fits := (Primrec.nat_lt.comp rank (Primrec.list_length.comp values)).decide
  have obs := (exactUnifiedNumericTerminal.1 f hf).comp (inst.pair rest).to_comp
  have checked : Computable (fun p : P => lowPoint f p.1 p.2) := by
    apply (Computable.cond fits.to_comp obs (Computable.const 0)).of_eq
    intro p
    by_cases h : p.1.1 < p.1.2.2.1.length <;> simp [lowPoint,h]
  exact checked.to₂

private theorem tableComputable (f : Nat → Nat) (hf : Computable f) : Computable (lowTable f) := by
  let P := LowArgs × Nat
  have indices : Primrec (fun p : LowArgs => List.range p.2.1) :=
    Primrec.list_range.comp (Primrec.fst.comp Primrec.snd)
  have index : Computable (Prod.snd : P → Nat) := Computable.snd
  have packet : Computable₂ (fun (p : LowArgs) a => (a,lowPoint f p a)) :=
    (index.pair ((pointComputable f hf).comp Computable.fst Computable.snd)).to₂
  exact BoundedSourceProgramsProof.computable_map indices.to_comp packet

private theorem hasRowsPrimitive : Primrec hasRows := by
  let A := Bool × List Row
  let P := A × (Row × Bool)
  have needle : Primrec (fun p : P => boolCode p.1.1) :=
    boolCodePrimitive.comp (Primrec.fst.comp Primrec.fst)
  have item : Primrec (fun p : P => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have next : Primrec (fun p : P => decide (p.2.1.2 = boolCode p.1.1) || p.2.2) :=
    Primrec.or.comp ((Primrec.eq.comp item needle).decide) (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : A → List Row))
    (Primrec.const false) next.to₂).of_eq
  intro p
  unfold hasRows
  generalize p.2 = rows
  induction rows with
  | nil => rfl
  | cons r rs ih => simp [List.foldr_cons,List.any_cons,ih]

theorem exactNumericFiniteLowLayout : ExactNumericFiniteLowLayout := by
  constructor
  · intro f hf
    have table := tableComputable f hf
    exact ⟨table,hasRowsPrimitive.to_comp.comp
      (Computable.snd.pair (table.comp Computable.fst))⟩
  · intro f p
    constructor
    · simp [lowTable,List.map_map,Function.comp_def]
    · intro a code
      rw [lowTable,List.mem_map]
      constructor
      · rintro ⟨k,kr,eq⟩
        have same : k = a := congrArg Prod.fst eq
        subst k
        exact ⟨List.mem_range.mp kr,(congrArg Prod.snd eq).symm⟩
      · rintro ⟨within,rfl⟩
        exact ⟨a,List.mem_range.mpr within,rfl⟩

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
