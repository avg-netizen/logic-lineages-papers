module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicAnnotation
public import LogicLineages.ComputabilityKnowledge.GorbowNameDictionaryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotationProof
open GorbowSyntax GorbowNameDictionary GorbowRevisionComposition GorbowAtomicAnnotation GorbowFreeSupport

private theorem getName {n m : Nat} (names : Fin n → Fin m) (j : Fin n) :
    (namesList names).getD j.val 0=(names j).val := by
  simp [namesList,List.getD_eq_getElem?_getD,j.isLt]

theorem uniqueCalibration : Comparators.GorbowAtomicAnnotation.UniqueCalibration := by
  intro n m names
  change decide (∀ i ∈ List.range (namesList names).length,
    (namesList names).idxOf ((namesList names).getD i 0)=i)=true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h i j hij
    have hi := h i.val (by simp [namesList,i.isLt])
    have hj := h j.val (by simp [namesList,j.isLt])
    rw [getName] at hi hj
    apply Fin.ext
    rw [← hi,← hj,hij]
  · intro h i hi
    have hib : i<n := by simpa [namesList] using List.mem_range.mp hi
    have hl : (namesList names).Nodup := List.nodup_ofFn.mpr (Fin.val_injective.comp h)
    have he := hl.idxOf_getElem i (by simp [namesList,hib])
    simpa [namesList,List.getD_eq_getElem?_getD,hib] using he

private theorem occursSupport (m : Nat) (R : Formula m) (i : Fin m) :
    GorbowSupportCode.occurs 1 m i.val (GorbowFormulaPrefixCode.encode R)=true ↔
      i.val ∈ formulaSupport R := by
  have hs := GorbowSupportCodeProof.scannerInvariant.2 m R i [] false
  have hu : GorbowSupportCode.occurs 1 m i.val (GorbowFormulaPrefixCode.encode R)=R.uses i := by
    simp only [GorbowSupportCode.occurs,i.isLt,ite_true,hs,Bool.false_or]
  rw [hu]
  exact (GorbowFreeSupportProof.usesCalibration.2 m R i).symm

private theorem coversIff (n m : Nat) (R : Formula m) (names : Fin n → Fin m) :
    Covers R names ↔ ∀ i, i∈formulaSupport R ↔ i∈namesList names := by
  unfold Covers
  constructor
  · intro h i
    rw [h]
    simp [namesList]
  · intro h
    ext i
    simpa [namesList] using h i

theorem coverCalibration : Comparators.GorbowAtomicAnnotation.CoverCalibration := by
  intro n m R names
  unfold coversNames
  rw [decide_eq_true_eq,coversIff]
  constructor
  · intro h i
    by_cases hi : i<m
    · exact (occursSupport m R ⟨i,hi⟩).symm.trans (h i (List.mem_range.mpr hi))
    · have hs : i∉formulaSupport R := fun hs => hi (GorbowFreeSupportProof.supportBound.2 m R i hs)
      have hn : i∉namesList names := by
        simp only [namesList,List.mem_ofFn]
        rintro ⟨j,hj⟩
        exact hi (hj ▸ (names j).isLt)
      simp [hs,hn]
  · intro h i hi
    exact (occursSupport m R ⟨i,List.mem_range.mp hi⟩).trans (h i)

private theorem atomCalibration {m : Nat} (R : Formula m) :
    (GorbowFormulaPrefixCode.encode R).headD 12<3 ↔ AtomicMinus R := by
  cases R <;> simp [GorbowFormulaPrefixCode.encode,AtomicMinus]

private theorem formulaValid {m : Nat} (R : Formula m) :
    GorbowSyntaxValidation.validFormula m (GorbowFormulaPrefixCode.encode R)=true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 m _).mpr
    ⟨R,(GorbowFormulaPrefixCodeProof.decoderExact m _ R).mpr rfl⟩

theorem originalCalibration : Comparators.GorbowAtomicAnnotation.OriginalCalibration := by
  intro n m R names hn hc ha
  have hb : boundedNames m (namesList names)=true := by
    simp only [boundedNames,decide_eq_true_eq,namesList,List.mem_ofFn]
    rintro i ⟨j,rfl⟩
    exact (names j).isLt
  simp only [valid,formulaValid,Bool.true_and,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨(atomCalibration R).mpr ha,hb⟩,(uniqueCalibration n m names).mpr hn⟩,
    (coverCalibration n m R names).mpr hc⟩

theorem exactDomain : Comparators.GorbowAtomicAnnotation.ExactDomain := by
  intro m raw ns
  constructor
  · intro h
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hv,ha⟩,hb⟩,hu⟩,hc⟩ := h
    obtain ⟨R,hR⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 m raw).mp hv
    have hr := (GorbowFormulaPrefixCodeProof.decoderExact m raw R).mp hR
    subst raw
    have hb' : ∀ i∈ns,i<m := by simpa only [boundedNames,decide_eq_true_eq] using hb
    let names : Fin ns.length → Fin m := fun j => ⟨ns[j.val],hb' _ (List.getElem_mem j.isLt)⟩
    have hn : ns=namesList names := by simp [namesList,names]
    refine ⟨R,names,rfl,hn,?_,?_,(atomCalibration R).mp ha⟩
    · exact (uniqueCalibration ns.length m names).mp (hn ▸ hu)
    · exact (coverCalibration ns.length m R names).mp (hn ▸ hc)
  · rintro ⟨R,names,hr,hn,hi,hc,ha⟩
    rw [hr,hn]
    exact originalCalibration _ _ R names hi hc ha

private theorem pr_bounded : Primrec (fun p : Nat × List Nat => boundedNames p.1 p.2) :=
  (Primrec.nat_lt : PrimrecRel (fun i m : Nat => i<m)).forall_mem_list.decide.comp Primrec.snd Primrec.fst
private theorem pr_unique : Primrec uniqueNames := by
  have hp : PrimrecRel (fun i : Nat => fun ns : List Nat => ns.idxOf (ns.getD i 0)=i) :=
    Primrec.eq.comp (Primrec.list_idxOf.comp ((Primrec.list_getD 0).comp Primrec.snd Primrec.fst)
      Primrec.snd) Primrec.fst
  exact hp.forall_mem_list.decide.comp (Primrec.list_range.comp Primrec.list_length) Primrec.id
private theorem pr_mem : PrimrecRel (fun i : Nat => fun ns : List Nat => i∈ns) := by
  have h := (Primrec.eq : PrimrecRel (fun a b : Nat => a=b)).exists_mem_list.comp Primrec.snd Primrec.fst
  exact h.of_eq (by intro p; simp)
private theorem pr_covers : Primrec (fun p : Nat × List Nat × List Nat => coversNames p.1 p.2.1 p.2.2) := by
  have ho : Primrec (fun p : Nat × (Nat × List Nat × List Nat) =>
      GorbowSupportCode.occurs 1 p.2.1 p.1 p.2.2.1) :=
    GorbowSupportCodeProof.uniformPrograms.2.2.1.comp
      ((Primrec.const 1).pair ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
  have hm : PrimrecPred (fun p : Nat × (Nat × List Nat × List Nat) => p.1∈p.2.2.2) :=
    pr_mem.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hp : PrimrecRel (fun i : Nat => fun p : Nat × List Nat × List Nat =>
      GorbowSupportCode.occurs 1 p.1 i p.2.1=true ↔ i∈p.2.2) :=
    (Primrec.eq.comp ho hm.decide).of_eq (by intro p; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq])
  exact hp.forall_mem_list.decide.comp (Primrec.list_range.comp Primrec.fst) Primrec.id
private theorem pr_valid : Primrec (fun p : Nat × List Nat × List Nat => valid p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Nat × List Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hv := GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp (Primrec.fst.pair hr)
  have hh : Primrec (fun p : Nat × List Nat × List Nat => p.2.1.headD 12) :=
    ((Primrec.list_getD 12).comp hr (Primrec.const 0)).of_eq (by intro p; cases p.2.1 <;> rfl)
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp hv ((Primrec.nat_lt.comp hh (Primrec.const 3)).decide))
    (pr_bounded.comp (Primrec.fst.pair hn))) (pr_unique.comp hn)) pr_covers

theorem uniformPrograms : Comparators.GorbowAtomicAnnotation.UniformPrograms :=
  ⟨pr_bounded,pr_unique,pr_covers,pr_valid⟩
theorem gorbowAtomicAnnotation : Comparators.GorbowAtomicAnnotation.Target :=
  ⟨uniqueCalibration,coverCalibration,exactDomain,originalCalibration,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotationProof
