module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowShiftTableProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowShiftProof
open NumberedWindowShiftAlgorithm NumberedWindowShiftTargets NumberedWindowShiftTableProof
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
theorem term (a c b : Nat) : ∀ (Q : NTerm) (d : Nat), encodeTerm Q + d ≤ b →
    (computed a c b (encodeTerm Q) d).1 = encodeTerm (shift a (c+d) Q)
  | .free t x,d,_ | .bottom t,d,_ => by
    simp only [shift,encodeTerm,computedNode,termParts]
    rw [encodePack]
  | .bound t i,d,_ => by
    simp only [shift,encodeTerm,computedNode,termParts]
    simp [encodePack,List.getD_eq_getElem?_getD]
  | .lam t q,d,h => by
    let fs := [encodeTy t,encodeTerm q]
    have hCode : encodeTerm q < encodeNode 2 fs := nodeBelow 2 fs _ (by simp [fs])
    change encodeNode 2 fs + d ≤ b at h
    have hChild : encodeTerm q + (d+1) ≤ b := by omega
    have ec := child a c b (d+1) 2 fs (encodeTerm q) (by simp [fs]) (by omega)
    change (computed a c b (encodeNode 2 fs) d).1 = _
    rw [computedNode]
    simp [termParts,List.getD_eq_getElem?_getD,fs,ec,term a c b q (d+1) hChild,shift,
      encodeTerm,Nat.add_assoc]
    rw [encodePack]
  | .ordinary f bs,d,h => by
    let fs := [encodeHead f,encodeArgs bs]
    have hCode : encodeArgs bs < encodeNode 4 fs := nodeBelow 4 fs _ (by simp [fs])
    change encodeNode 4 fs + d ≤ b at h
    have ec := child a c b d 4 fs (encodeArgs bs) (by simp [fs]) (by omega)
    change (computed a c b (encodeNode 4 fs) d).1 = _
    rw [computedNode]
    simp [termParts,List.getD_eq_getElem?_getD,fs,ec,args a c b bs d (by omega),shift,
      encodeTerm]
    rw [encodePack]
  | .numbered f t k bs es,d,h => by
    let fs := [encodeHead f,encodeTy t,k,encodeArgs bs,encodeArgs es]
    have hBs : encodeArgs bs < encodeNode 5 fs := nodeBelow 5 fs _ (by simp [fs])
    have hEs : encodeArgs es < encodeNode 5 fs := nodeBelow 5 fs _ (by simp [fs])
    change encodeNode 5 fs + d ≤ b at h
    have eb := child a c b d 5 fs (encodeArgs bs) (by simp [fs]) (by omega)
    have ee := child a c b d 5 fs (encodeArgs es) (by simp [fs]) (by omega)
    change (computed a c b (encodeNode 5 fs) d).1 = _
    rw [computedNode]
    simp [termParts,List.getD_eq_getElem?_getD,fs,eb,ee,
      args a c b bs d (by omega),args a c b es d (by omega),shift,encodeTerm]
    rw [encodePack]
  | .auxApp s t q u,d,h => by
    let fs := [encodeTy s,encodeTy t,encodeTerm q,encodeTerm u]
    have hQ : encodeTerm q < encodeNode 6 fs := nodeBelow 6 fs _ (by simp [fs])
    have hU : encodeTerm u < encodeNode 6 fs := nodeBelow 6 fs _ (by simp [fs])
    change encodeNode 6 fs + d ≤ b at h
    have eq := child a c b d 6 fs (encodeTerm q) (by simp [fs]) (by omega)
    have eu := child a c b d 6 fs (encodeTerm u) (by simp [fs]) (by omega)
    change (computed a c b (encodeNode 6 fs) d).1 = _
    rw [computedNode]
    simp [termParts,List.getD_eq_getElem?_getD,fs,eq,eu,
      term a c b q d (by omega),term a c b u d (by omega),shift,encodeTerm]
    rw [encodePack]

theorem args (a c b : Nat) : ∀ (qs : NArgs) (d : Nat), encodeArgs qs + d ≤ b →
    (computed a c b (encodeArgs qs) d).2 = encodeArgs (shiftArgs a (c+d) qs)
  | .nil,d,_ => rfl
  | .cons q qs,d,h => by
    have hQ := (pairBounds (encodeTerm q) (encodeArgs qs)).1
    have hQs := (pairBounds (encodeTerm q) (encodeArgs qs)).2
    change pair (encodeTerm q) (encodeArgs qs) + 1 + d ≤ b at h
    change (computed a c b (pair (encodeTerm q) (encodeArgs qs)+1) d).2 = _
    rw [computedCons a c b d _ _ (by omega),
      term a c b q d (by omega),args a c b qs d (by omega)]
    rfl
end

theorem matrix : ExactShiftMatrix :=
  ⟨fun a c b d Q h => term a c b Q d h,
   fun a c b d qs h => args a c b qs d h⟩

end LogicLineages.PersistentMarking.NumberedWindowShiftProof
