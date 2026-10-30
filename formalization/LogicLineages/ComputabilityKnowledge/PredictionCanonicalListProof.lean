module

public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListTargets
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalListProof
open PredictionLearning PredictionCanonicalList PredictionCanonicalListTargets

theorem ordinaryNumberingCalibration : OrdinaryNumberingCalibration := by
  exact ⟨fun c => Denumerable.ofNat_encode c, fun i => Denumerable.encode_ofNat i⟩

private theorem same_refl (c : Code) : SameFunction c c := fun _ => rfl
private theorem same_symm {c d : Code} (h : SameFunction c d) : SameFunction d c :=
  fun n => (h n).symm
private theorem same_trans {a b c : Code} (h : SameFunction a b) (h' : SameFunction b c) :
    SameFunction a c := fun n => (h n).trans (h' n)
private theorem total_transport {c d : Code} (h : SameFunction c d) (hd : TotalNat d) : TotalNat c := by
  intro n
  rw [h n]
  exact hd n

theorem uniqueLeastRepresentative : UniqueLeastRepresentative := by
  classical
  intro c hc
  have hex : ∃ i, SameFunction (codeAt i) c :=
    ⟨Encodable.encode c, by rw [(ordinaryNumberingCalibration).1]; exact same_refl c⟩
  let i := Nat.find hex
  have hi : SameFunction (codeAt i) c := Nat.find_spec hex
  have hr : Representative i := by
    refine ⟨total_transport hi hc, fun j hj hjf => ?_⟩
    exact Nat.find_min hex hj (same_trans hjf hi)
  refine ⟨i, ⟨hr, hi⟩, ?_⟩
  intro j hj
  apply Nat.le_antisymm
  · by_contra h
    exact hj.1.2 i (by omega) (same_trans hi (same_symm hj.2))
  · by_contra h
    exact hr.2 j (by omega) (same_trans hj.2 (same_symm hi))

private theorem const_total (n : Nat) : TotalNat (Nat.Partrec.Code.const n) := by
  intro x
  exact ⟨n, by rw [Nat.Partrec.Code.eval_const]; exact Part.mem_some_iff.mpr rfl⟩

theorem infinitelyManyRepresentatives : InfinitelyManyRepresentatives := by
  classical
  have hex : ∀ n : Nat, ∃ i, Representative i ∧ SameFunction (codeAt i) (Nat.Partrec.Code.const n) :=
    fun n => (uniqueLeastRepresentative _ (const_total n)).exists
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro a b hab
    have heq : Part.some a = Part.some b := by
      calc
        Part.some a = Nat.Partrec.Code.eval (codeAt (f a)) 0 := by
          rw [(hf a).2 0, Nat.Partrec.Code.eval_const]
        _ = Nat.Partrec.Code.eval (codeAt (f b)) 0 := by rw [hab]
        _ = Part.some b := by rw [(hf b).2 0, Nat.Partrec.Code.eval_const]
    exact Part.some_injective heq
  exact Set.infinite_of_injective_forall_mem hinj (fun n => (hf n).1)

theorem strictCanonicalEnumeration : StrictCanonicalEnumeration := by
  exact ⟨Nat.nth_strictMono infinitelyManyRepresentatives,
    Nat.nth_mem_of_infinite infinitelyManyRepresentatives⟩

theorem exhaustiveCanonicalCodes : ExhaustiveCanonicalCodes := by
  intro c hc
  obtain ⟨i, hi, huniq⟩ := uniqueLeastRepresentative c hc
  obtain ⟨n, hn⟩ := Nat.subset_range_nth (p := Representative) hi.1
  have hn' : canonicalIndex n = i := hn
  refine ⟨n, ?_, ?_⟩
  · change SameFunction (codeAt (canonicalIndex n)) c
    rw [hn']
    exact hi.2
  · intro m hm
    apply strictCanonicalEnumeration.1.injective
    exact (huniq (canonicalIndex m) ⟨strictCanonicalEnumeration.2 m, hm⟩).trans hn'.symm

theorem exhaustiveTotalComputableFunctions : ExhaustiveTotalComputableFunctions := by
  intro f hf
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  have ht : TotalNat c := by
    intro x
    refine ⟨f x, ?_⟩
    rw [hc]
    exact Part.mem_some_iff.mpr rfl
  obtain ⟨n, hn, hu⟩ := exhaustiveCanonicalCodes c ht
  refine ⟨n, fun x => (hn x).trans (congrFun hc x), ?_⟩
  intro m hm
  exact hu m (fun x => (hm x).trans (congrFun hc x).symm)

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalListProof
