module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSingletonTableProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowShiftChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonProof
open NumberedWindowSingletonAlgorithm NumberedWindowArithmeticSingletonTargets NumberedWindowArithmeticSingletonTableProof
open NumberedWindowShiftAlgorithm (earlier)
open NumberedWindowShiftTableProof (encodePack)
open NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticFields
open NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticPair (pair)

private theorem child (amount cutoff bound offset tag : Nat) (fields : List Nat) (code : Nat)
    (mem : code ∈ fields) (h : offset ≤ bound) :
    earlier (table amount cutoff bound (encodeNode tag fields)) code offset =
      computed amount cutoff bound code offset :=
  earlierExact amount cutoff bound (nodeBelow tag fields code mem) h

mutual
theorem term (a : NTerm) (c b : Nat) : ∀ (Q : NTerm) (d : Nat), encodeTerm Q + d ≤ b →
    (computed (encodeTerm a) c b (encodeTerm Q) d).1 = encodeTerm (substitute (.cons a .nil) (c+d) Q)
  | .free t x,d,_ | .bottom t,d,_ => by
    simp [encodeTerm,computedNode,termParts,NumberedWindowShiftAlgorithm.termParts,substitute,← encodePack]
  | .bound t i,d,_ => by
    have lift : (NumberedWindowShiftAlgorithm.output (c+d) 0 (encodeTerm a)).1 =
        some (encodeTerm (shift (c+d) 0 a)) := by
      rw [NumberedWindowShiftChecks.exact_ShiftOutput]
      simp [NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.2.1]
    by_cases inner : i < c+d
    · simp [encodeTerm,computedNode,termParts,substitute,inner,← encodePack,List.getD_eq_getElem?_getD]
    · by_cases hit : i = c+d
      · subst i
        simp [computedNode,termParts,substitute,NArgs.get,encodeTerm,← encodePack,lift,List.getD_eq_getElem?_getD]
      · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show i - (c+d) ≠ 0 by omega)
        simp [computedNode,termParts,substitute,inner,hit,hj,NArgs.get,NArgs.length,
          encodeTerm,← encodePack,List.getD_eq_getElem?_getD,Nat.pred_eq_sub_one]
  | .lam t q,d,h => by
    let fs := [encodeTy t,encodeTerm q]
    have hCode : encodeTerm q < encodeNode 2 fs := nodeBelow 2 fs _ (by simp [fs])
    change encodeNode 2 fs + d ≤ b at h
    have hChild : encodeTerm q + (d+1) ≤ b := by omega
    have ec := child (encodeTerm a) c b (d+1) 2 fs (encodeTerm q) (by simp [fs]) (by omega)
    change (computed (encodeTerm a) c b (encodeNode 2 fs) d).1 = _
    rw [computedNode]
    simp [termParts,NumberedWindowShiftAlgorithm.termParts,List.getD_eq_getElem?_getD,fs,ec,term a c b q (d+1) hChild,substitute,
      encodeTerm,← encodePack,Nat.add_assoc]
  | .ordinary f bs,d,h => by
    let fs := [encodeHead f,encodeArgs bs]
    have hCode : encodeArgs bs < encodeNode 4 fs := nodeBelow 4 fs _ (by simp [fs])
    change encodeNode 4 fs + d ≤ b at h
    have ec := child (encodeTerm a) c b d 4 fs (encodeArgs bs) (by simp [fs]) (by omega)
    change (computed (encodeTerm a) c b (encodeNode 4 fs) d).1 = _
    rw [computedNode]
    simp [termParts,NumberedWindowShiftAlgorithm.termParts,List.getD_eq_getElem?_getD,fs,ec,args a c b bs d (by omega),substitute,
      encodeTerm,← encodePack]
  | .numbered f t k bs es,d,h => by
    let fs := [encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es]
    have hBs : encodeArgs bs < encodeNode 5 fs := nodeBelow 5 fs _ (by simp [fs])
    have hEs : encodeArgs es < encodeNode 5 fs := nodeBelow 5 fs _ (by simp [fs])
    change encodeNode 5 fs + d ≤ b at h
    have eb := child (encodeTerm a) c b d 5 fs (encodeArgs bs) (by simp [fs]) (by omega)
    have ee := child (encodeTerm a) c b d 5 fs (encodeArgs es) (by simp [fs]) (by omega)
    change (computed (encodeTerm a) c b (encodeNode 5 fs) d).1 = _
    rw [computedNode]
    simp [termParts,NumberedWindowShiftAlgorithm.termParts,List.getD_eq_getElem?_getD,fs,eb,ee,
      args a c b bs d (by omega),args a c b es d (by omega),substitute,encodeTerm,← encodePack]
  | .auxApp s t q u,d,h => by
    let fs := [encodeTy s,encodeTy t,encodeTerm q,encodeTerm u]
    have hQ : encodeTerm q < encodeNode 6 fs := nodeBelow 6 fs _ (by simp [fs])
    have hU : encodeTerm u < encodeNode 6 fs := nodeBelow 6 fs _ (by simp [fs])
    change encodeNode 6 fs + d ≤ b at h
    have eq := child (encodeTerm a) c b d 6 fs (encodeTerm q) (by simp [fs]) (by omega)
    have eu := child (encodeTerm a) c b d 6 fs (encodeTerm u) (by simp [fs]) (by omega)
    change (computed (encodeTerm a) c b (encodeNode 6 fs) d).1 = _
    rw [computedNode]
    simp [termParts,NumberedWindowShiftAlgorithm.termParts,List.getD_eq_getElem?_getD,fs,eq,eu,
      term a c b q d (by omega),term a c b u d (by omega),substitute,encodeTerm,← encodePack]

theorem args (a : NTerm) (c b : Nat) : ∀ (qs : NArgs) (d : Nat), encodeArgs qs + d ≤ b →
    (computed (encodeTerm a) c b (encodeArgs qs) d).2 = encodeArgs (substituteArgs (.cons a .nil) (c+d) qs)
  | .nil,d,_ => rfl
  | .cons q qs,d,h => by
    have hQ := (pairBounds (encodeTerm q) (encodeArgs qs)).1
    have hQs := (pairBounds (encodeTerm q) (encodeArgs qs)).2
    change pair (encodeTerm q) (encodeArgs qs) + 1 + d ≤ b at h
    change (computed (encodeTerm a) c b (pair (encodeTerm q) (encodeArgs qs)+1) d).2 = _
    rw [computedCons (encodeTerm a) c b d _ _ (by omega),
      term a c b q d (by omega),args a c b qs d (by omega)]
    rfl
end

theorem matrix : ExactSingletonMatrix :=
  ⟨fun a c b d Q h => term a c b Q d h,
   fun a c b d qs h => args a c b qs d h⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonProof
