module
public import LogicLineages.PermittedControl.SelectedCountOnlyClassTargets
import LogicLineages.PermittedControl.CountTransferCoreProof
import LogicLineages.PermittedControl.FixedEntryClosedScanActualProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedCountOnlyClass
open OrdinalComparison FieldComparison InnerTerminationTargets

theorem prefixNotationExact : PrefixNotationExact := by
  have hn : omegaSquareNote.1.repr = Ordinal.omega0 ^ (2 : Nat) := by
    simpa [omegaSquareNote,ONote.repr] using Ordinal.opow_natCast Ordinal.omega0 2
  have ho : omegaSquareNote.1.repr = Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
    hn.trans (Ordinal.opow_natCast Ordinal.omega0 2).symm
  refine ⟨ho,?_⟩
  intro mu
  change (mu + omegaSquareNote).1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0})
  rw [note_add_repr,ho]

private theorem actualCoreRecordExists (f : Nat → Nat) (B : Nat)
    (hf : SelectedWithThreshold f B) {r : Nat} (ρ : Fin r → Nat) (c : Occurrence r)
    (hlong : LongField (.entry 0 c.1.1 c.1.2))
    (htail : max (actualOrdinalNorm c.1.1.1.repr) (actualOrdinalNorm c.1.2.1.repr + 3) ≤ ρ c.2) :
    ∃ i k q : Nat, ActualCoreRecord f ρ c i k q := by
  let lam := c.1.1
  let mu := c.1.2
  let x := ρ c.2
  let eta := prefixTarget mu
  have heta := prefixNotationExact.2 mu
  have hlim : Order.IsSuccLimit eta.1.repr := by
    rw [show eta.1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0}) from heta]
    exact Ordinal.isSuccLimit_add _ square_facts.2.2
  obtain ⟨hle,i,k,hi,hk,horbit,hdoubled⟩ :=
    countCore f B hf lam.1.repr mu.1.repr x
      (rawNotation_repr_lt_epsilonZero lam.1) hlong.1 hlong.2.1 hlong.2.2.1 hlong.2.2.2 htail
  let q := entryNormAt f (countInitial lam.1.repr x) i
  have hprefix : FirstEntry f (countInitial lam.1.repr x) eta.1.repr i := by
    rw [show eta.1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0}) from heta]
    exact hi
  have hread : prefixRead f ρ c = some (some (q,i)) :=
    ((fixedEntryClosedActual f lam eta x (Or.inr hlim)).1 q i).mpr ⟨hprefix,rfl⟩
  have hkey : fullKey f ρ c = some (some (f q)) := by
    rw [fullKey,hread] <;> rfl
  have hle' : eta.1.repr ≤ lam.1.repr := by
    rw [show eta.1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0}) from heta]
    exact hle
  exact ⟨i,k,q,hle',hprefix,hk,rfl,horbit,hread,hkey,hdoubled⟩

theorem actualClassExtraction : ActualClassExtraction := by
  intro f B hf r R ρ seed _hρ hseed hguards
  dsimp only
  have hrec (c : Occurrence r) (hc : c ∈ R.count.support) :
      ∃ i k q : Nat, ActualCoreRecord f ρ c i k q :=
    actualCoreRecordExists f B hf ρ c (hguards c hc).1 (hguards c hc).2
  obtain ⟨i₀,k₀,q₀,hs⟩ := hrec seed hseed
  have hk0 : fullKey f ρ seed = some (some (f q₀)) := hs.2.2.2.2.2.2.1
  have hmem (c : Occurrence r) :
      c ∈ members R f ρ seed ↔ c ∈ R.count.support ∧ fullKey f ρ c = some (some (f q₀)) := by
    simp only [members,hk0,Finset.mem_filter]
  have hseed' : seed ∈ members R f ρ seed := (hmem seed).mpr ⟨hseed,hk0⟩
  have hne : (members R f ρ seed).Nonempty := ⟨seed,hseed'⟩
  refine ⟨fun c hc => ((hmem c).mp hc).1,hseed',?_,i₀,k₀,q₀,hs,?_⟩
  · simp only [zeroEligible,decide_eq_true_eq,hne,true_and,signedWeight]
  · intro c hc
    obtain ⟨i,k,q,ha⟩ := hrec c hc
    have hk : fullKey f ρ c = some (some (f q)) := ha.2.2.2.2.2.2.1
    exact ⟨i,k,q,ha,by simp only [hmem,hc,true_and,hk,Option.some.injEq]⟩

theorem fullSelectedCountOnlyClass : FullSelectedCountOnlyClass :=
  ⟨prefixNotationExact,actualClassExtraction⟩

end LogicLineages.PermittedControl.SelectedCountOnlyClass
