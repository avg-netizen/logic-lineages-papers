module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerTargets
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsProof
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldProof
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.Proof
open CommonHeadLargeRow CommonHeadLargeGuards

private theorem disjunction_variables (ps:List Formula) (i:Nat) :
    i∈(disjunction ps).variables ↔ ∃p∈ps,i∈p.variables := by
  induction ps with
  | nil => simp [disjunction,Formula.variables]
  | cons p ps ih =>
    change i∈p.variables++(disjunction ps).variables ↔ _
    rw [List.mem_append,ih]
    simp

theorem originalSupport : Targets.ExactOriginalSupport := by
  intro fuel
  induction fuel with
  | zero =>
    intro h K cs desired i hi
    dsimp only [compileFuel] at hi
    split at hi <;> simp [Formula.variables] at hi
  | succ fuel ih =>
    intro h K cs desired j hj
    change j∈(largeFormula K cs desired).variables++_ at hj
    rcases List.mem_append.mp hj with hj|hj
    · exact CommonHeadLargeGuards.Proof.originalInputSupport K cs desired j hj
    · obtain ⟨p,hp,hj⟩:=(disjunction_variables _ j).mp hj
      obtain ⟨i,hi,hp⟩:=List.mem_flatMap.mp hp
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hp
      have hi':i<cs.length:=List.mem_range.mp hi
      let child:=compileFuel fuel h (childConstant h K cs i c) (cs.eraseIdx i) desired
      exact (CommonHeadGuardReindex.Proof.exactGuardedFold 0 K cs ⟨i,hi'⟩ c child
        (ih h (childConstant h K cs i c) (cs.eraseIdx i) desired)).1 j hj

private theorem threshold_input (K:Int) (cs:List Int) (ν:Nat→Nat) :
    threshold K (inputRow cs ν)=originalThreshold K cs := by
  have h:=congrArg (fun xs:List Int=>(xs.map Int.natAbs).sum) (List.zipIdx_map_fst 0 cs)
  simp only [List.map_map,Function.comp_def] at h
  simpa only [threshold,originalThreshold,mass,inputRow,List.map_map,Function.comp_def,h]

private theorem child_exact (rho:NONote) (K:Int) (cs:List Int) (i c:Nat) (hi:i<cs.length) :
    childConstant (rawNoteEncode rho.1) K cs i c=K+cs[i]*(actualHeadValue rho.1.repr c:Int) := by
  unfold childConstant
  rw [List.getD_eq_getElem cs 0 hi,(CommonHeadSmallFold.Proof.closedEvaluation.2 rho c).1]

private theorem small_membership (rho:NONote) (K:Int) (cs:List Int) (c:Nat) :
    c∈smallNumerals (rawNoteEncode rho.1) K cs ↔
      c<originalThreshold K cs ∧ actualOrdinalNorm rho.1.repr≤c := by
  have hnorm:rawNormCode (rawNoteEncode rho.1)=actualOrdinalNorm rho.1.repr:=by
    rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence rho]
  simp only [smallNumerals,CommonHeadSmallFold.smallValuesCode,List.mem_filter,List.mem_range,
    decide_eq_true_eq,originalThreshold,hnorm]

theorem exactFuel : Targets.ExactFuelCompiler := by
  intro fuel
  induction fuel with
  | zero =>
    intro rho hlim K cs desired ν hlen hg
    have he:cs=[]:=List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst cs
    by_cases hs:Int.sign K=desired <;> simp [compileFuel,Formula.eval,inputRow,value,hs]
  | succ fuel ih =>
    intro rho hlim K cs desired ν hlen hg
    have branch (i:Nat) (hi:i<cs.length) (c:Nat) :
      (CommonHeadGuardReindex.guarded i c (compileFuel fuel (rawNoteEncode rho.1)
        (childConstant (rawNoteEncode rho.1) K cs i c) (cs.eraseIdx i) desired)).eval ν ↔
        ν i=c ∧ Int.sign (value rho.1.repr K (inputRow cs ν))=desired := by
      have hcLen:(cs.eraseIdx i).length≤fuel:=by rw [List.length_eraseIdx_of_lt hi];omega
      have hcGenuine:∀j<(cs.eraseIdx i).length,
          actualOrdinalNorm rho.1.repr≤(ν∘CommonHeadGuardReindex.skip i) j:=by
        intro j hj
        exact hg _ ((CommonHeadGuardReindex.Proof.exactDeletion cs ⟨i,hi⟩ ν).2 j hj).1
      have hchild:=ih rho hlim (childConstant (rawNoteEncode rho.1) K cs i c)
        (cs.eraseIdx i) desired (ν∘CommonHeadGuardReindex.skip i) hcLen hcGenuine
      rw [CommonHeadGuardReindex.Proof.guarded_eval,hchild]
      have fold (he:ν i=c) : value rho.1.repr
          (childConstant (rawNoteEncode rho.1) K cs i c)
          (inputRow (cs.eraseIdx i) (ν∘CommonHeadGuardReindex.skip i))=
            value rho.1.repr K (inputRow cs ν) := by
        rw [child_exact rho K cs i c hi]
        exact (CommonHeadGuardReindex.Proof.exactGuardedFold rho.1.repr K cs ⟨i,hi⟩ c
          (compileFuel fuel (rawNoteEncode rho.1) (childConstant (rawNoteEncode rho.1) K cs i c)
            (cs.eraseIdx i) desired)
          (originalSupport fuel _ _ _ _)).2 ν |>.2 he
      constructor
      · rintro ⟨he,hs⟩
        exact ⟨he,by simpa only [fold he] using hs⟩
      · rintro ⟨he,hs⟩
        exact ⟨he,by simpa only [fold he] using hs⟩
    have hlarge:=CommonHeadLargeGuards.Proof.exactActualLargeFormula rho.1.repr
      (rawNotation_repr_lt_epsilonZero rho.1) hlim K cs desired ν hg
    change ((largeFormula K cs desired).eval ν ∨ _ ) ↔ _
    rw [hlarge,CommonHeadLargeGuards.Proof.disjunction_eval]
    constructor
    · rintro (⟨_,hs⟩|⟨p,hp,hpν⟩)
      · exact hs
      · obtain ⟨i,hi,hp⟩:=List.mem_flatMap.mp hp
        obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hp
        exact ((branch i (List.mem_range.mp hi) c).mp hpν).2
    · intro hs
      by_cases hall:∀i<cs.length,originalThreshold K cs≤ν i
      · exact Or.inl ⟨hall,hs⟩
      · right
        obtain ⟨i,hi⟩:=not_forall.mp hall
        have hi':i<cs.length:=by by_contra hn;exact hi (fun hh=>(hn hh).elim)
        have hsmall:ν i<originalThreshold K cs:=by
          apply lt_of_not_ge
          intro hb
          exact hi (fun _=>hb)
        have hc:ν i∈smallNumerals (rawNoteEncode rho.1) K cs:=
          (small_membership rho K cs (ν i)).mpr ⟨hsmall,hg i hi'⟩
        refine ⟨_,List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi',List.mem_map.mpr ⟨ν i,hc,rfl⟩⟩,?_⟩
        exact (branch i hi' (ν i)).mpr ⟨rfl,hs⟩

theorem exactSourceRow : Targets.ExactSourceRowCompiler := by
  intro rho hlim K cs desired ν hg
  exact exactFuel cs.length rho hlim K cs desired ν le_rfl hg
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler.Proof
