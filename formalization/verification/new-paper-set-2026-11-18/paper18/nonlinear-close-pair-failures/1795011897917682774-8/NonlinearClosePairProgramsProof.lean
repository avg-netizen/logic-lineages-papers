module
public import LogicLineages.StandardControlCurrent.NonlinearClosePairProof
public import LogicLineages.StandardControlCurrent.InverseCutSyntaxProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeComputationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NonlinearClosePairProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearClosePair
open InverseCutSyntaxProof

private theorem varP {α : Type} [Primcodable α] {x : α → Nat} (hx : Primrec x) :
    Primrec (fun q => WindowCode.var (x q)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) hx) (Primrec.const 1)
private theorem phiP {α : Type} [Primcodable α] {x : α → Nat} (hx : Primrec x) :
    Primrec (fun q => WindowCode.phi (x q)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) hx) (Primrec.const 6)

private theorem guardP {α : Type} [Primcodable α] {x k C v : α → Nat}
    (hx : Primrec x) (hk : Primrec k) (hC : Primrec C) (hv : Primrec v) :
    Primrec (fun q => guardCode (x q) (k q) (C q) (v q)) :=
  andCodeP
    (leCodeP (phiP hv) (phiP (addCodeP (varP hx) (numeralCodeP hk))))
    (lessCodeP (phiP (addCodeP (varP hx) (numeralCodeP hk))) (mulCodeP hC (phiP hv)))

private theorem candidateP {α : Type} [Primcodable α] {v k j : α → Nat}
    (hv : Primrec v) (hk : Primrec k) (hj : Primrec j) :
    Primrec (fun q => candidateCode (v q) (k q) (j q)) :=
  subCodeP (addCodeP hv (numeralCodeP hj)) (numeralCodeP hk)

private theorem branchP {α : Type} [Primcodable α] {x k C v p j : α → Nat}
    (hx : Primrec x) (hk : Primrec k) (hC : Primrec C) (hv : Primrec v)
    (hp : Primrec p) (hj : Primrec j) :
    Computable (fun q => branchCode (x q) (k q) (C q) (v q) (p q) (j q)) := by
  have hl := leCodeP (numeralCodeP hk) (addCodeP hv (numeralCodeP hj))
  have hr := candidateP hv hk hj
  have hg := andCodeP (guardP hx hk hC hv) hp
  have hs := WindowCodeProof.matrix_computable.comp (hg.to_comp.pair (hx.to_comp.pair hr.to_comp))
  have ha : Primrec₂ WindowCode.conjunction := andCodeP Primrec.fst Primrec.snd
  exact ha.to_comp.comp hl.to_comp hs

private theorem anyP : Primrec WindowCode.any :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (orCodeP (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private theorem mapC {A B C : Type} [Primcodable A] [Primcodable B]
    [Primcodable C] [Inhabited B] {xs : A → List B} {f : A → B → C}
    (hx : Computable xs) (hf : Computable₂ f) : Computable (fun a => (xs a).map (f a)) := by
  have hs : Computable₂ (fun a : A => fun p : B × List C => f a p.1 :: p.2) :=
    Primrec.list_cons.to_comp.comp
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (LayeredComparison.ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr_cons, List.map_cons, ih]

theorem programs : NonlinearClosePairTargets.Programs := by
  have termC : Computable (fun q : Nat × Nat × Nat => WindowCode.termSubstitute q.1 q.2.1 q.2.2) :=
    WindowCodeProof.term_computable.comp ((Computable.snd.comp Computable.snd).pair
      (Computable.fst.pair (Computable.fst.comp Computable.snd)))
  have matrixC : Computable (fun q : Nat × Nat × Nat => WindowCode.matrixSubstitute q.1 q.2.1 q.2.2) :=
    WindowCodeProof.matrix_computable.comp ((Computable.snd.comp Computable.snd).pair
      (Computable.fst.pair (Computable.fst.comp Computable.snd)))
  refine ⟨termC,matrixC,?_⟩
  have hx : Primrec (fun q : Input => q.1) := Primrec.fst
  have hk : Primrec (fun q : Input => q.2.1) := Primrec.fst.comp Primrec.snd
  have hC : Primrec (fun q : Input => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun q : Input => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hp : Primrec (fun q : Input => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Computable₂ (fun q : Input => fun j : Nat => branchCode q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 j) :=
    branchP (hx.comp Primrec.fst) (hk.comp Primrec.fst) (hC.comp Primrec.fst)
      (hv.comp Primrec.fst) (hp.comp Primrec.fst) Primrec.snd
  have hl : Computable (fun q : Input => List.range (q.2.2.1+1)) :=
    (Primrec.list_range.comp (Primrec.nat_add.comp hC (Primrec.const 1))).to_comp
  exact anyP.to_comp.comp (mapC hl hb)

theorem full : NonlinearClosePairTargets.Full :=
  ⟨actualWidth, substitution, parameterElimination, support, boundaryCases, literalCode, programs⟩
end LogicLineages.StandardControlCurrent.NonlinearClosePairProof
