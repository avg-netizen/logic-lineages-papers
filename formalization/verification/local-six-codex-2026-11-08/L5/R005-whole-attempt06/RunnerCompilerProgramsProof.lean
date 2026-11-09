module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerLeastProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
open PolynomialGraphCompletion WordLinearDecisionCompletion AlgorithmPrograms
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

def finishPackage (s : Runner.EncodedState) : EncodedPackage := (s.1,s.2.2)
def invalidPackage : EncodedPackage := (0,[])

noncomputable def solve (D maximum : Nat) (r : Row) : EncodedPackage :=
  if Runner.admitted D r then finishPackage (run D maximum r (Runner.leastFuel D maximum r))
  else invalidPackage

def combineCase (left right : CaseData) : CaseData :=
  (6*Nat.pair left.1 right.1+4,left.2++right.2)

def combinePackage (left right : EncodedPackage) : EncodedPackage :=
  (max left.1 right.1,left.2.flatMap (fun l => right.2.map (combineCase l)))

def emptyFamily : EncodedPackage := (0,[(0,[])])

noncomputable def compile (D maximum : Nat) (rows : List Row) : EncodedPackage :=
  rows.foldr (fun r out => combinePackage (solve D maximum r) out) emptyFamily

theorem encodePackage_eq (p : Package) : encodePackage p = (p.tail,p.cases.map encodeCase) := rfl

theorem solve_calibration (D maximum : Nat) (r : Row) :
    solve D maximum r = encodePackage (Runner.solve D maximum r) := by
  cases ha : Runner.admitted D r <;>
    simp [solve,Runner.solve,ha,invalidPackage,Runner.invalidPackage,finishPackage,
      Runner.finish,run_calibration,Runner.encodeState,encodePackage_eq,encodeCase]

theorem combineCase_calibration (left right : RowCase) :
    combineCase (encodeCase left) (encodeCase right) = encodeCase (Runner.combineCase left right) := by
  simp only [combineCase,encodeCase,Runner.combineCase,Formula.encode,List.map_append]

theorem combinePackage_calibration (left right : Package) :
    combinePackage (encodePackage left) (encodePackage right) = encodePackage (Runner.combinePackage left right) := by
  simp only [encodePackage_eq,combinePackage,Runner.combinePackage,List.map_flatMap,
    List.flatMap_map,List.map_map,Function.comp_def,combineCase_calibration]

theorem compile_calibration (D maximum : Nat) (rows : List Row) :
    compile D maximum rows = encodePackage (Runner.compile D maximum rows) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      change combinePackage (solve D maximum r) (compile D maximum rows) =
        encodePackage (Runner.combinePackage (Runner.solve D maximum r) (Runner.compile D maximum rows))
      rw [solve_calibration,ih,combinePackage_calibration]

theorem finishPackage_primitive : Primrec finishPackage :=
  Primrec.fst.pair (Primrec.snd.comp Primrec.snd)

theorem solve_computable : Computable (fun p : Nat × Nat × Row => solve p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Row
  have hD : Computable (fun p : A => p.1) := Computable.fst
  have hm : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hr : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have ha := admitted_primitive.to_comp.comp hD hr
  have hrun := run_computable.comp (hD.pair (hm.pair (hr.pair leastFuel_computable)))
  apply (Computable.cond ha (finishPackage_primitive.to_comp.comp hrun)
    (Computable.const invalidPackage)).of_eq
  intro p
  cases ha : Runner.admitted p.1 p.2.2 <;> simp [solve,ha,Bool.cond_eq_ite]

theorem combineCase_primitive : Primrec₂ combineCase :=
  (conjunction_encode_primitive.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem combinePackage_primitive : Primrec₂ combinePackage := by
  let A := EncodedPackage × EncodedPackage
  have hi : Primrec (fun p : A × CaseData => p.1.2.2.map (combineCase p.2)) :=
    Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (combineCase_primitive.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hcases := Primrec.list_flatMap (Primrec.snd.comp Primrec.fst) hi.to₂
  exact (Primrec.nat_max.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair hcases

theorem compile_computable :
    Computable (fun p : Nat × Nat × List Row => compile p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × List Row
  have hD : Computable (fun p : A => p.1) := Computable.fst
  have hm : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hr : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hsolve : Computable (fun p : A × (Row × EncodedPackage) => solve p.1.1 p.1.2.1 p.2.1) :=
    solve_computable.comp ((hD.comp Computable.fst).pair
      ((hm.comp Computable.fst).pair (Computable.fst.comp Computable.snd)))
  have hstep : Computable₂ (fun p : A => fun state : Row × EncodedPackage =>
      combinePackage (solve p.1 p.2.1 state.1) state.2) :=
    combinePackage_primitive.to_comp.comp hsolve (Computable.snd.comp Computable.snd)
  exact computable_foldr ((0,[]) : Row) hr (Computable.const emptyFamily) hstep

theorem actualFamilyProgram : RunnerTargets.ActualFamilyProgram := by
  apply compile_computable.of_eq
  intro p
  exact compile_calibration p.1 p.2.1 p.2.2

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
