module

public import LogicLineages.ComputabilityKnowledge.Comparators.CircuitComparisonEffectivity
public import LogicLineages.ComputabilityKnowledge.CircuitReductionEffectivityProof

@[expose] public section

/-! External Codex continuation proof: both strict and weak coded comparison
maps have primitive-recursive certificates. A length-framed parser is proved
correct on the existing system codec; no expression computability oracle is used. -/
namespace LogicLineages.ComputabilityKnowledge.CircuitComparisonEffectivityProof

open PositiveExpression CircuitReduction CircuitComparison
open Comparators.ExponentialGap

private abbrev PairCodes := List (List Nat × List Nat)

private theorem pr_cons {α : Type} [Primcodable α] {a : α → Nat} {b : α → List Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => a x :: b x) :=
  Primrec.list_cons.comp ha hb

theorem outputCodecFaithful : Comparators.CircuitComparisonEffectivity.OutputCodecFaithful := by
  rintro ⟨d,a,b⟩ ⟨e,c,f⟩ h
  have h' : d = e ∧ encodeSystem [(a,b)] = encodeSystem [(c,f)] := List.cons.inj h
  have hp : [(a,b)] = [(c,f)] := CircuitReductionEffectivityProof.outputCodecFaithful h'.2
  have hab : (a,b) = (c,f) := (List.cons.inj hp).1
  cases h'.1
  cases hab
  rfl

theorem strictCorrespondence : Comparators.CircuitComparisonEffectivity.StrictCorrespondence := by
  intro c
  simp [strictCode, CircuitReductionEffectivityProof.inputCodecFaithful c]

theorem weakCorrespondence : Comparators.CircuitComparisonEffectivity.WeakCorrespondence := by
  intro c
  simp [weakCode, CircuitReductionEffectivityProof.inputCodecFaithful c]

/-- Total parser of length frames. On malformed inputs arbitrary truncation is
harmless: only correctness on encodeSystem is used by the certified compiler. -/
private def splitSystem : List Nat → PairCodes
  | m :: n :: rest => (rest.take m, (rest.drop m).take n) :: splitSystem (rest.drop (m+n))
  | _ => []
termination_by code => code.length
decreasing_by simp_wf; omega

private theorem pr_splitSystem : Primrec splitSystem := by
  let children : List Nat → List (List Nat) := fun xs =>
    if 2 ≤ xs.length then [(xs.drop 2).drop (xs.getD 0 0 + xs.getD 1 0)] else []
  let assemble : List Nat → List PairCodes → Option PairCodes := fun xs rs =>
    some (if 2 ≤ xs.length then
      (((xs.drop 2).take (xs.getD 0 0)), ((xs.drop 2).drop (xs.getD 0 0)).take (xs.getD 1 0)) :: rs.head!
      else [])
  have hg (i : Nat) : Primrec (fun xs : List Nat => xs.getD i 0) :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const i)
  have hd : Primrec (fun xs : List Nat => xs.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) Primrec.id
  have ht := Primrec.list_drop.comp (Primrec.nat_add.comp (hg 0) (hg 1)) hd
  have hcond : PrimrecPred (fun xs : List Nat => 2 ≤ xs.length) :=
    Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length
  have hchildren : Primrec children :=
    Primrec.ite hcond (Primrec.list_cons.comp ht (Primrec.const [])) (Primrec.const [])
  have hpair : Primrec (fun xs : List Nat =>
      ((xs.drop 2).take (xs.getD 0 0), ((xs.drop 2).drop (xs.getD 0 0)).take (xs.getD 1 0))) :=
    (Primrec.list_take.comp (hg 0) hd).pair
      (Primrec.list_take.comp (hg 1) (Primrec.list_drop.comp (hg 0) hd))
  have hassemble : Primrec₂ assemble :=
    (Primrec.option_some.comp (Primrec.ite (hcond.comp Primrec.fst)
      (Primrec.list_cons.comp (hpair.comp Primrec.fst) (Primrec.list_headI.comp Primrec.snd))
      (Primrec.const []))).to₂
  apply Primrec.nat_omega_rec' splitSystem Primrec.list_length hchildren hassemble
  · intro xs ys hy
    by_cases h : 2 ≤ xs.length
    · simp [children,h] at hy
      subst ys
      simp only [List.length_drop]
      omega
    · simp [children,h] at hy
  · intro xs
    cases xs with
    | nil => simp [assemble,children,splitSystem]
    | cons m xs =>
      cases xs with
      | nil => simp [assemble,children,splitSystem]
      | cons n xs =>
        have hd2 (k : Nat) : (m :: n :: xs).drop (2 + k) = xs.drop k := by
          rw [Nat.add_comm]
          rfl
        simp [assemble,children,splitSystem,hd2]

private theorem split_encode (s : System) :
    splitSystem (encodeSystem s) = s.map (fun p => (encodeExpr p.1,encodeExpr p.2)) := by
  induction s with
  | nil => simp [encodeSystem,splitSystem]
  | cons p ps ih =>
    simp only [encodeSystem, splitSystem]
    have hd : ((encodeExpr p.1 ++ encodeExpr p.2) ++ encodeSystem ps).drop
        ((encodeExpr p.1).length + (encodeExpr p.2).length) = encodeSystem ps := by
      simpa only [List.length_append] using (show ((encodeExpr p.1 ++ encodeExpr p.2) ++ encodeSystem ps).drop
        (encodeExpr p.1 ++ encodeExpr p.2).length = encodeSystem ps from List.drop_left)
    simp only [hd, ih, List.map_cons]
    congr 1 <;> simp [List.append_assoc]

private def leftPairCode (p : List Nat × List Nat) : List Nat :=
  [2,3,2] ++ p.1 ++ p.1 ++ [0,3,2] ++ p.2 ++ p.2 ++ [0]
private def rightPairCode (p : List Nat × List Nat) : List Nat :=
  [3,2,2] ++ p.1 ++ p.2 ++ [0,0]

private def leftCode (s : PairCodes) : List Nat :=
  s.foldr (fun p acc => 2 :: (leftPairCode p ++ acc)) [0]
private def rightCode (s : PairCodes) : List Nat :=
  s.foldr (fun p acc => 2 :: (rightPairCode p ++ acc)) [0]

private theorem pr_leftPairCode : Primrec leftPairCode := by
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (Primrec.list_append.comp (Primrec.const [2,3,2]) Primrec.fst) Primrec.fst)
          (Primrec.const [0,3,2])) Primrec.snd) Primrec.snd) (Primrec.const [0])

private theorem pr_rightPairCode : Primrec rightPairCode := by
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.const [3,2,2]) Primrec.fst) Primrec.snd)
    (Primrec.const [0,0])

private theorem pr_leftCode : Primrec leftCode :=
  Primrec.list_foldr Primrec.id (Primrec.const [0])
    (pr_cons (Primrec.const 2)
      (Primrec.list_append.comp (pr_leftPairCode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))).to₂

private theorem pr_rightCode : Primrec rightCode :=
  Primrec.list_foldr Primrec.id (Primrec.const [0])
    (pr_cons (Primrec.const 2)
      (Primrec.list_append.comp (pr_rightPairCode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))).to₂

private theorem leftCode_correct (s : System) :
    leftCode (s.map (fun p => (encodeExpr p.1,encodeExpr p.2))) = encodeExpr (systemLeft s) := by
  induction s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, leftCode, List.foldr_cons] at *
    rw [ih]
    simp [systemLeft,leftPair,encodeExpr,leftPairCode,List.append_assoc]

private theorem rightCode_correct (s : System) :
    rightCode (s.map (fun p => (encodeExpr p.1,encodeExpr p.2))) = encodeExpr (systemRight s) := by
  induction s with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, rightCode, List.foldr_cons] at *
    rw [ih]
    simp [systemRight,rightPair,encodeExpr,rightPairCode,List.append_assoc]

private def frame (d : Nat) (a b : List Nat) : List Nat :=
  d :: a.length :: b.length :: (a ++ b)

private theorem pr_frame : Primrec (fun p : Nat × List Nat × List Nat => frame p.1 p.2.1 p.2.2) :=
  pr_cons Primrec.fst (pr_cons (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
    (pr_cons (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))

private def rawBound (xs : List Nat) : Nat := xs.getD 0 0 + 9 * ((xs.length - 3) / 3)

private theorem pr_rawBound : Primrec rawBound :=
  Primrec.nat_add.comp ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 0))
    (Primrec.nat_mul.comp (Primrec.const 9)
      (Primrec.nat_div.comp (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 3)) (Primrec.const 3)))

private theorem decode_length : ∀ (xs : List Nat) (gs : List Gate),
    decodeGates xs = some gs → xs.length = 3 * gs.length
  | [], gs, h => by simp [decodeGates] at h; subst gs; rfl
  | [tag], gs, h => by simp [decodeGates] at h
  | [tag,x], gs, h => by simp [decodeGates] at h
  | tag :: x :: y :: rest, gs, h => by
    have help (g : Gate) (he : (decodeGates rest).map (g :: ·) = some gs) :
        (tag :: x :: y :: rest).length = 3 * gs.length := by
      cases hr : decodeGates rest with
      | none => simp [hr] at he
      | some tail =>
        simp [hr] at he
        subst gs
        have hi := decode_length rest tail hr
        simp only [List.length_cons]
        omega
    cases tag with
    | zero =>
      cases y with
      | zero => exact help (.constant x) h
      | succ y => simp [decodeGates] at h
    | succ tag =>
      cases tag with
      | zero => exact help (.add x y) h
      | succ tag =>
        cases tag with
        | zero => exact help (.mul x y) h
        | succ tag => simp [decodeGates] at h
termination_by xs => xs.length

private theorem rawBound_correct (xs : List Nat) (c : Circuit)
    (h : decodeCircuit xs = some c) : rawBound xs = variableBound c := by
  cases xs with
  | nil => simp [decodeCircuit] at h
  | cons n xs =>
    cases xs with
    | nil => simp [decodeCircuit] at h
    | cons l xs =>
      cases xs with
      | nil => simp [decodeCircuit] at h
      | cons r rest =>
        cases hg : decodeGates rest with
        | none => simp [decodeCircuit,hg] at h
        | some gs =>
          simp [decodeCircuit,hg] at h
          subst c
          have hlen := decode_length rest gs hg
          simp [rawBound,variableBound,hlen,Nat.mul_div_right]

private def transformed (weak : Bool) (xs system : List Nat) : List Nat :=
  let pairs := splitSystem system
  let lo := rightCode pairs
  let hi := leftCode pairs
  frame (rawBound xs) (if weak then 2 :: (lo ++ [0]) else lo) hi

private theorem pr_transformed (weak : Bool) :
    Primrec (fun p : List Nat × List Nat => transformed weak p.1 p.2) := by
  have hs := pr_splitSystem.comp (Primrec.snd : Primrec (fun p : List Nat × List Nat => p.2))
  have hlo := pr_rightCode.comp hs
  have hhi := pr_leftCode.comp hs
  cases weak
  · exact pr_frame.comp ((pr_rawBound.comp Primrec.fst).pair (hlo.pair hhi))
  · exact pr_frame.comp ((pr_rawBound.comp Primrec.fst).pair
      ((pr_cons (Primrec.const 2) (Primrec.list_append.comp hlo (Primrec.const [0]))).pair hhi))

private theorem transformed_correct (weak : Bool) (xs : List Nat) (c : Circuit)
    (h : decodeCircuit xs = some c) : transformed weak xs (encodeSystem (compile c)) =
      encodeComparison (if weak then weakOutput c else strictOutput c) := by
  simp only [transformed, split_encode, leftCode_correct, rightCode_correct, rawBound_correct xs c h]
  cases weak <;> simp [frame,encodeComparison,strictOutput,weakOutput,lower,upper,weakLower,encodeSystem,encodeExpr]

private theorem pr_code (weak : Bool) : Primrec (fun xs =>
    (decodeCircuit xs).map (fun c => encodeComparison (if weak then weakOutput c else strictOutput c))) := by
  have h : Primrec (fun xs => (compileCode xs).map (transformed weak xs)) :=
    Primrec.option_map CircuitReductionEffectivityProof.compilerPrimrec (pr_transformed weak).to₂
  apply h.of_eq
  intro xs
  cases hc : decodeCircuit xs with
  | none => simp [compileCode,hc]
  | some c => simp [compileCode,hc,transformed_correct weak xs c hc]

theorem strictPrimrec : Primrec strictCode := by
  exact (pr_code false).of_eq (fun _ => rfl)

theorem weakPrimrec : Primrec weakCode := by
  exact (pr_code true).of_eq (fun _ => rfl)

theorem circuitComparisonEffectivity : Comparators.CircuitComparisonEffectivity.Target :=
  ⟨outputCodecFaithful,strictCorrespondence,weakCorrespondence,strictPrimrec.to_comp,weakPrimrec.to_comp⟩

end LogicLineages.ComputabilityKnowledge.CircuitComparisonEffectivityProof
