module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProgramListProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion
open LayeredComparison.IntegerAlgorithms

theorem scaleRow_primitive : Primrec₂ scaleRow := by
  let A := Int × Row
  have hi : Primrec (fun p : A × (Int × Token) => (p.1.1*p.2.1,p.2.2)) :=
    (LayeredComparison.IntegerAlgorithms.Proof.mul_primitive.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : A => p.2.2.map (fun a => (p.1*a.1,a.2))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hi.to₂
  exact (LayeredComparison.IntegerAlgorithms.Proof.mul_primitive.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair hs

theorem shiftConstant_primitive : Primrec₂ shiftConstant :=
  (LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).pair
    (Primrec.snd.comp Primrec.snd)

theorem renamePairRow_primitive :
    Primrec (fun p : Nat × Nat × Row => renamePairRow p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Row
  have hl : Primrec (fun p : A × (Int × Token) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : A × (Int × Token) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hn : Primrec (fun p : A × (Int × Token) => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun p : A × (Int × Token) =>
      (p.2.1,if p.2.2.1 = 0 then p.1.1 else p.1.2.1,p.2.2.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      ((Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) hl hr).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd))).pair
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hi.to₂)

theorem nonnegative_encode_primitive :
    Primrec (fun r : Row => Formula.encode (.atom (.nonnegative r))) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6)
      (Primrec.encode.comp ((Primrec.const (0 : Nat)).pair
        ((Primrec.const (0 : Nat)).pair Primrec.id))))
    (Primrec.const 2)

theorem conjunction_encode_primitive : Primrec₂ (fun p q : Nat => 6*Nat.pair p q+4) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const 4)

theorem disjunction_encode_primitive : Primrec₂ (fun p q : Nat => 6*Nat.pair p q+5) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const 5)

theorem signFormula_encode_primitive :
    Primrec (fun p : Nat × Row => Formula.encode (signFormula p.1 p.2)) := by
  have hnegative : Primrec (fun p : Nat × Row => scaleRow (-1) p.2) :=
    scaleRow_primitive.comp (Primrec.const (-1 : Int)) Primrec.snd
  have hzero : Primrec (fun p : Nat × Row =>
      Formula.encode (.atom (.nonnegative (shiftConstant (-1) (scaleRow (-1) p.2))))) :=
    nonnegative_encode_primitive.comp
      (shiftConstant_primitive.comp (Primrec.const (-1 : Int)) hnegative)
  have hone : Primrec (fun p : Nat × Row => Formula.encode
      (.conj (.atom (.nonnegative p.2)) (.atom (.nonnegative (scaleRow (-1) p.2))))) :=
    conjunction_encode_primitive.comp (nonnegative_encode_primitive.comp Primrec.snd)
      (nonnegative_encode_primitive.comp hnegative)
  have htwo : Primrec (fun p : Nat × Row =>
      Formula.encode (.atom (.nonnegative (shiftConstant (-1) p.2)))) :=
    nonnegative_encode_primitive.comp
      (shiftConstant_primitive.comp (Primrec.const (-1 : Int)) Primrec.snd)
  apply (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) hzero
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) hone
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) htwo (Primrec.const 1)))).of_eq
  intro p
  by_cases h0 : p.1 = 0 <;> by_cases h1 : p.1 = 1 <;> by_cases h2 : p.1 = 2 <;>
    simp [signFormula,Formula.encode,h0,h1,h2]

def conjunctionCodes (codes : List Nat) : Nat :=
  codes.foldr (fun p q => 6*Nat.pair p q+4) 0

def disjunctionCodes (codes : List Nat) : Nat :=
  codes.foldr (fun p q => 6*Nat.pair p q+5) 1

theorem conjunctionCodes_primitive : Primrec conjunctionCodes :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (conjunction_encode_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem disjunctionCodes_primitive : Primrec disjunctionCodes :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (disjunction_encode_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem disjoin_encode (ps : List Formula) :
    Formula.encode (disjoin ps) = disjunctionCodes (ps.map Formula.encode) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [disjoin,disjunctionCodes,List.foldr_cons,List.map_cons,
      Formula.encode] using congrArg (fun q => 6*Nat.pair (Formula.encode p) q+5) ih

theorem conjoin_encode (ps : List Formula) :
    Formula.encode (Algorithm.conjoin ps) = conjunctionCodes (ps.map Formula.encode) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [Algorithm.conjoin,conjunctionCodes,List.foldr_cons,
      List.map_cons,Formula.encode] using congrArg (fun q => 6*Nat.pair (Formula.encode p) q+4) ih

attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

/-- Exact encoded ordered-name guards, composed with the already checked
total original pair compiler. No Encodable instance for semantic Formula is
introduced; the actual emitted numeric formula code is computed directly. -/
theorem orderedGuard_encode_computable {α : Type} [Primcodable α]
    (D : α → Nat) (u v : α → Token) (desired : α → Nat)
    (hD : Computable D) (hu : Computable u) (hv : Computable v)
    (hs : Computable desired) :
    Computable (fun a => Formula.encode (orderedGuard (D a) (u a) (v a) (desired a))) := by
  let out := fun a => FullWordGuardCompletion.compile (D a) ((u a).2,(v a).2)
  have hout : Computable out := FullWordGuardCompletion.CompilerProgramsProof.compile_computable.comp
    (hD.pair ((Computable.snd.comp hu).pair (Computable.snd.comp hv)))
  have hrow : Computable (fun a => renamePairRow (u a).1 (v a).1
      (FullWordGuardCompletion.packageRow (out a))) :=
    renamePairRow_primitive.to_comp.comp ((Computable.fst.comp hu).pair
      ((Computable.fst.comp hv).pair (Computable.fst.comp (Computable.snd.comp hout))))
  have hguards : Computable (fun a => FullWordGuardCompletion.packageGuards (out a)) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hout))
  have hsigns : Computable (fun a => FullWordGuardCompletion.guardAt
      (FullWordGuardCompletion.packageGuards (out a)) (desired a)) :=
    FullWordGuardCompletion.ComparisonProgramsProof.guardAt_primitive.to_comp.comp (hguards.pair hs)
  have hcode : Computable₂ (fun a s => Formula.encode (signFormula s
      (renamePairRow (u a).1 (v a).1 (FullWordGuardCompletion.packageRow (out a))))) :=
    (signFormula_encode_primitive.to_comp.comp
      (Computable.snd.pair (hrow.comp Computable.fst))).to₂
  apply (disjunctionCodes_primitive.to_comp.comp (computable_map 0 hsigns hcode)).of_eq
  intro a
  simp only [orderedGuard,disjoin_encode,List.map_map,Function.comp_def]
  rfl

theorem literalDifference_primitive : Primrec₂ literalDifference :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair Primrec.fst)
      (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair Primrec.snd) (Primrec.const [])))

theorem comparisonGuard_encode_computable {α : Type} [Primcodable α]
    (D maximum : α → Nat) (u v : α → Token) (desired : α → Nat)
    (hD : Computable D) (hmaximum : Computable maximum) (hu : Computable u)
    (hv : Computable v) (hs : Computable desired) :
    Computable (fun a => Formula.encode
      (comparisonGuard (D a) (maximum a) (u a) (v a) (desired a))) := by
  let out := fun a => FullWordGuardCompletion.compile (D a) ((u a).2,(v a).2)
  have hout : Computable out := FullWordGuardCompletion.CompilerProgramsProof.compile_computable.comp
    (hD.pair ((Computable.snd.comp hu).pair (Computable.snd.comp hv)))
  have hsame : Computable (fun a => FullWordGuardCompletion.packageSame (out a)) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hout)))
  have huMax : Computable (fun a => (u a).1 == maximum a) :=
    Primrec.beq.to_comp.comp (Computable.fst.comp hu) hmaximum
  have hvMax : Computable (fun a => (v a).1 == maximum a) :=
    Primrec.beq.to_comp.comp (Computable.fst.comp hv) hmaximum
  have hfixed : Computable (fun a => if FullWordGuardCompletion.packageSame (out a) = desired a
      then (0 : Nat) else 1) := by
    apply (Computable.cond (Primrec.beq.to_comp.comp hsame hs)
      (Computable.const 0) (Computable.const 1)).of_eq
    intro a
    by_cases he : FullWordGuardCompletion.packageSame (out a) = desired a <;>
      simp [Bool.cond_eq_ite,he]
  have hforward := orderedGuard_encode_computable D u v desired hD hu hv hs
  have hreverse := orderedGuard_encode_computable D v u
    (fun a => FullWordGuardCompletion.reverseOrder (desired a)) hD hv hu
    (FullWordGuardCompletion.ComparisonProgramsProof.reverseOrder_primitive.to_comp.comp hs)
  have hraw : Computable (fun a => Formula.encode (signFormula (desired a)
      (literalDifference (u a) (v a)))) :=
    signFormula_encode_primitive.to_comp.comp
      (hs.pair (literalDifference_primitive.to_comp.comp hu hv))
  apply (Computable.cond huMax (Computable.cond hvMax hfixed hforward)
    (Computable.cond hvMax hreverse hraw)).of_eq
  intro a
  by_cases hmu : (u a).1 = maximum a <;> by_cases hmv : (v a).1 = maximum a <;>
    by_cases hsame : FullWordGuardCompletion.packageSame
      (FullWordGuardCompletion.compile (D a) ((u a).2,(v a).2)) = desired a <;>
    simp [comparisonGuard,hmu,hmv,hsame,Formula.encode,out,Bool.cond_eq_ite]

theorem pairCutoff_computable {α : Type} [Primcodable α]
    (D : α → Nat) (u v : α → Token) (hD : Computable D)
    (hu : Computable u) (hv : Computable v) :
    Computable (fun a => pairCutoff (D a) (u a) (v a)) := by
  have hout := FullWordGuardCompletion.CompilerProgramsProof.compile_computable.comp
    (hD.pair ((Computable.snd.comp hu).pair (Computable.snd.comp hv)))
  exact Primrec.nat_max.to_comp.comp (Computable.fst.comp hout)
    (Primrec.nat_max.to_comp.comp
      (WordGuardCompletion.Proof.wordTail_primitive.to_comp.comp (Computable.snd.comp hu))
      (WordGuardCompletion.Proof.wordTail_primitive.to_comp.comp (Computable.snd.comp hv)))

theorem comparisonCutoff_computable {α : Type} [Primcodable α]
    (D maximum : α → Nat) (u v : α → Token) (hD : Computable D)
    (hmaximum : Computable maximum) (hu : Computable u) (hv : Computable v) :
    Computable (fun a => comparisonCutoff (D a) (maximum a) (u a) (v a)) := by
  have huMax : Computable (fun a => (u a).1 == maximum a) :=
    Primrec.beq.to_comp.comp (Computable.fst.comp hu) hmaximum
  have hvMax : Computable (fun a => (v a).1 == maximum a) :=
    Primrec.beq.to_comp.comp (Computable.fst.comp hv) hmaximum
  have hf := pairCutoff_computable D u v hD hu hv
  have hr := pairCutoff_computable D v u hD hv hu
  have hraw := Primrec.nat_max.to_comp.comp
    (WordGuardCompletion.Proof.wordTail_primitive.to_comp.comp (Computable.snd.comp hu))
    (WordGuardCompletion.Proof.wordTail_primitive.to_comp.comp (Computable.snd.comp hv))
  apply (Computable.cond huMax hf (Computable.cond hvMax hr hraw)).of_eq
  intro a
  by_cases hmu : (u a).1 = maximum a <;> by_cases hmv : (v a).1 = maximum a <;>
    simp [comparisonCutoff,hmu,hmv,Bool.cond_eq_ite]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
