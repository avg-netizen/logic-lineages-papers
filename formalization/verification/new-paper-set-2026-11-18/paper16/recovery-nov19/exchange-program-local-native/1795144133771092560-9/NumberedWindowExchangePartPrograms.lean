module

public import LogicLineages.PersistentMarking.NumberedWindowExchangeProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowExchangePartPrograms
open LogicLineages.ComputabilityKnowledge NumberedWindowExchangeAtoms NumberedWindowExchangeAlgorithm
open NumberedWindowFieldAlgorithm NumberedWindowSyntaxShapePrograms (anyOption)
open NumberedWindowLexicalRequirementPrograms (eqBool)
open NumberedWindowHeadDeclarationPrograms (choose declarationPrim)

theorem pairPrim : Primrec₂ NumberedWindowPairAlgorithm.pair :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.nat_add Primrec.nat_add) Primrec.fst

theorem anyTwo {δ α β} [Primcodable δ] [Primcodable α] [Primcodable β]
    {f : δ → Option α} {g : δ → Option β} {h : δ × α × β → Bool}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun d => (f d).any (fun a => (g d).any (fun b => h (d,a,b)))) :=
  anyOption hf (anyOption (hg.comp Primrec.fst)
    (hh.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂).to₂

private theorem permutation : Primrec₂ (fun (xs ys : List Nat) => decide (xs.Perm ys)) := by
  have count : Primrec₂ (fun (xs : List Nat) (a : Nat) => xs.count a) := by
    have h := Primrec.list_length.comp (PrimrecRel.listFilter (Primrec.eq : PrimrecRel (Eq : Nat → Nat → Prop)))
    apply h.to₂.of_eq
    intro xs a
    have same : (fun x : Nat => decide (x = a)) = (fun x => x == a) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp
    simpa only [List.count_eq_length_filter] using congrArg List.length (congrArg (fun filter => xs.filter filter) same)
  have same : PrimrecRel (fun (a : Nat) (p : List Nat × List Nat) => p.1.count a = p.2.count a) :=
    Primrec.eq.comp (count.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (count.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
  have bounded := same.forall_mem_list.comp (Primrec.list_append.comp Primrec.fst Primrec.snd) Primrec.id
  apply (bounded.of_eq ?_).decide
  intro p
  rw [List.perm_iff_count]
  constructor
  · intro h a
    by_cases ha : a ∈ p.1 ++ p.2
    · exact h a ha
    · have h₁ : a ∉ p.1 := fun h => ha (List.mem_append_left _ h)
      have h₂ : a ∉ p.2 := fun h => ha (List.mem_append_right _ h)
      simp [List.count_eq_zero_of_not_mem h₁, List.count_eq_zero_of_not_mem h₂]
  · exact fun h a _ => h a

private theorem bagPrim : Primrec₂ bag := by
  have fields : Primrec unpack := Primrec.encode_iff.mp ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr
    NumberedWindowFieldProgramChecks.exact_OrderedFieldPrograms.2)
  exact anyTwo (fields.comp Primrec.fst) (fields.comp Primrec.snd)
    (permutation.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

private theorem allowedPrim : Primrec (fun p : HeadPairs × Nat × Nat => allowed p.1 p.2.1 p.2.2) := by
  have mem : PrimrecRel (fun (xs : HeadPairs) (a : Nat × Nat) => a ∈ xs) :=
    (Primrec.eq : PrimrecRel (Eq : Nat × Nat → Nat × Nat → Prop)).exists_mem_list.of_eq (by simp)
  exact mem.decide

abbrev Env := HeadPairs × List Row
abbrev Node := Nat × List Nat

theorem partsPrim : Primrec (fun p : Env × Node × Node =>
    parts p.1.1 p.1.2 p.2.1.1 p.2.2.1 p.2.1.2 p.2.2.2) := by
  let P := Env × Node × Node
  have left : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have right : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  let x (n : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp left) (Primrec.const n)
  let y (n : Nat) := (Primrec.list_getD 0).comp (Primrec.snd.comp right) (Primrec.const n)
  let equal (n : Nat) := eqBool.comp (x n) (y n)
  let rel (n : Nat) := (Primrec.list_getD (false,false)).comp (Primrec.snd.comp Primrec.fst) (pairPrim.comp (x n) (y n))
  let base (n : Nat) := bagPrim.comp (x n) (y n)
  let heads := allowedPrim.comp ((Primrec.fst.comp Primrec.fst).pair ((x 0).pair (y 0)))
  let result := eqBool.comp (Primrec.fst.comp (declarationPrim.comp (x 0))) (Primrec.fst.comp (declarationPrim.comp (y 0)))
  let andP {f g : P → Bool} (hf : Primrec f) (hg : Primrec g) := Primrec.and.comp hf hg
  let orP {f g : P → Bool} (hf : Primrec f) (hg : Primrec g) := Primrec.or.comp hf hg
  let lam := andP (equal 0) (Primrec.fst.comp (rel 1))
  let ord := orP (andP (andP heads result) (base 1)) (andP (equal 0) (Primrec.snd.comp (rel 1)))
  let num := andP (andP (equal 1) (equal 2)) (orP (andP (andP heads (base 3)) (equal 4))
    (andP (equal 0) (orP (andP (Primrec.snd.comp (rel 3)) (equal 4)) (andP (equal 3) (Primrec.snd.comp (rel 4))))))
  let app := andP (andP (equal 0) (equal 1)) (orP (andP (Primrec.fst.comp (rel 2)) (equal 3))
    (andP (equal 2) (Primrec.fst.comp (rel 3))))
  have tag := Primrec.fst.comp left
  have body := choose tag 2 lam (choose tag 4 ord (choose tag 5 num (choose tag 6 app (Primrec.const false))))
  apply (Primrec.ite (Primrec.eq.comp tag (Primrec.fst.comp right)) body (Primrec.const false)).of_eq
  rintro ⟨env,⟨i,fs⟩,j,gs⟩
  by_cases h : i=j
  · subst j
    rcases i with _ | _ | _ | _ | _ | _ | _ | n <;> simp [parts]
  · simp [parts,h]
end LogicLineages.PersistentMarking.NumberedWindowExchangePartPrograms
