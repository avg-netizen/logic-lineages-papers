module
public import LogicLineages.StandardControlCurrent.ComputableRankedProof
public import Mathlib.Data.List.Permutation
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrencePermutationPrograms

def insertSlices (t : Nat) (tail : List Nat) : List Nat → List (List Nat)
  | [] => []
  | y::ys => (t::y::(ys++tail)) :: (insertSlices t tail ys).map (y::·)

theorem slices_calibration (t : Nat) (tail ys : List Nat) :
    insertSlices t tail ys=(List.permutationsAux2 t tail [] ys id).2 := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    rw [insertSlices,List.permutationsAux2_snd_cons]
    simp only [id_eq]
    rw [←List.map_permutationsAux2,ih]

theorem slices_primitive : Primrec (fun q : Nat × List Nat × List Nat => insertSlices q.1 q.2.1 q.2.2) := by
  have step : Primrec₂ (fun q : Nat × List Nat × List Nat => fun s : Nat × List Nat × List (List Nat) =>
      (q.1::s.1::(s.2.1++q.2.1)) :: s.2.2.map (s.1::·)) := by
    have t := Primrec.fst.comp Primrec.fst
    have y := Primrec.fst.comp Primrec.snd
    have ys := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have tail := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have rest := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hhead := Primrec.list_cons.comp t (Primrec.list_cons.comp y (Primrec.list_append.comp ys tail))
    have hmap := Primrec.list_map rest (Primrec.list_cons.comp (y.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_cons.comp hhead hmap
  apply (Primrec.list_rec (Primrec.snd.comp Primrec.snd) (Primrec.const []) step).of_eq
  intro q
  induction q.2.2 with
  | nil => rfl
  | cons y ys ih => simp only [insertSlices,ih]

abbrev Input := List Nat × List Nat
def rank (q : Input) : Nat := (q.1.length+q.2.length+1)^2+q.1.length
def children (q : Input) : List Input :=
  match q.1 with
  | [] => []
  | t::ts => [(ts,t::q.2),(q.2,[])]
def assemble (q : Input) (answers : List (List (List Nat))) : Option (List (List Nat)) :=
  match q.1 with
  | [] => some []
  | t::ts => some ((q.2::answers[1]?.getD []).foldr
      (fun y r => insertSlices t ts y ++ r) (answers[0]?.getD []))

theorem rank_primitive : Primrec rank :=
  ((Primrec.nat_pow.comp ((Primrec.list_length.comp Primrec.fst).add
    (Primrec.list_length.comp Primrec.snd) |>.add (Primrec.const 1)) (Primrec.const 2)).add
    (Primrec.list_length.comp Primrec.fst)

theorem children_primitive : Primrec children := by
  apply Primrec.list_casesOn Primrec.fst (Primrec.const [])
  have ts := Primrec.snd.comp Primrec.snd
  have t := Primrec.fst.comp Primrec.snd
  have is := Primrec.snd.comp Primrec.fst
  exact Primrec.list_cons.comp (ts.pair (Primrec.list_cons.comp t is))
    (Primrec.list_cons.comp (is.pair (Primrec.const [])) (Primrec.const []))

theorem child_rank (q c : Input) (hc : c∈children q) : rank c<rank q := by
  rcases q with ⟨ts,is⟩
  cases ts with
  | nil => simp [children] at hc
  | cons t ts =>
    simp only [children,List.mem_cons,List.mem_singleton] at hc
    rcases hc with rfl | rfl
    · simp only [rank,List.length_cons]
      nlinarith
    · simp only [rank,List.length_cons,List.length_nil]
      nlinarith

theorem assemble_equation (q : Input) :
    assemble q ((children q).map (fun q => List.permutationsAux q.1 q.2)) =
      some (List.permutationsAux q.1 q.2) := by
  rcases q with ⟨ts,is⟩
  cases ts with
  | nil => simp [assemble,List.permutationsAux_nil]
  | cons t ts =>
    simp only [assemble,children,List.map_cons,List.map_nil,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,List.permutationsAux_cons,List.permutations]
    congr 1
    apply List.foldr_congr
    intro y r hy
    rw [slices_calibration,List.permutationsAux2_append]

theorem assemble_primitive : Primrec (fun a : Input × List (List (List Nat)) => assemble a.1 a.2) := by
  let A := Input × List (List (List Nat))
  have input : Primrec (fun a : A => a.1.1) := Primrec.fst.comp Primrec.fst
  have old : Primrec (fun a : A => a.1.2) := Primrec.snd.comp Primrec.fst
  have first : Primrec (fun a : A => a.2[0]?.getD []) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0)) (Primrec.const [])
  have second : Primrec (fun a : A => a.2[1]?.getD []) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 1)) (Primrec.const [])
  have t : Primrec (fun a : A => a.1.1.head!) := Primrec.list_headI.comp input
  have ts : Primrec (fun a : A => a.1.1.tail) := Primrec.list_tail.comp input
  have step : Primrec₂ (fun a : A => fun yr : List Nat × List (List Nat) =>
      insertSlices a.1.1.head! a.1.1.tail yr.1 ++ yr.2) :=
    Primrec.list_append.comp
      (slices_primitive.comp ((t.comp Primrec.fst).pair ((ts.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  have folded := Primrec.list_foldr (Primrec.list_cons.comp old second) first step
  have result := Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp input) (Primrec.const 0))
    (Primrec.const (some ([] : List (List Nat)))) (Primrec.option_some.comp folded)
  apply result.of_eq
  intro a
  cases a.1.1 <;> simp [assemble,List.head!,List.headI]

theorem auxiliary_computable : Computable (fun q : Input => List.permutationsAux q.1 q.2) :=
  ComputableRankedProof.ranked Input (List (List Nat))
    (fun q => List.permutationsAux q.1 q.2) rank children assemble
    rank_primitive children_primitive assemble_primitive.to_comp child_rank assemble_equation

theorem permutations_computable : Computable (List.permutations : List Nat → List (List Nat)) :=
  Primrec.list_cons.to_comp.comp Computable.id
    (auxiliary_computable.comp (Computable.id.pair (Computable.const [])))

end LogicLineages.StandardControlCurrent.OrderedOccurrencePermutationPrograms
