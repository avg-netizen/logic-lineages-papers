module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverLayerProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowHeadEnumerationProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationGuardProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSimpleProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowPrimaryCoverSyntax NumberedWindowPrimaryCoverLayerProof
open NumberedWindowHeadEnumerationTargets
open NumberedWindowPreservationGuardProof (TermGuard consParts)
open NumberedWindowNumberedDomainProof (ArgsGuard)
open NumberedWindowApplicationDomainProof (subtypeSelf)

abbrev TermAt (S : Spine.Signature) (K : List Ty) (m n : Nat) (Q : NTerm) : Prop :=
  TermGuard S K Q → (termBounds Q).numeral ≤ m → (termBounds Q).nodes ≤ n →
    Q ∈ terms (admittedHeads S K) K m n

abbrev ArgsAt (S : Spine.Signature) (K : List Ty) (m n : Nat) (qs : NArgs) : Prop :=
  ArgsGuard S K qs → (argsBounds qs).numeral ≤ m → (argsBounds qs).nodes ≤ n →
    qs ∈ cells (admittedHeads S K) K m n

theorem admittedMem {S K f} (h : HeadInWindow S K f) : f ∈ admittedHeads S K :=
  ((NumberedWindowHeadEnumerationProof.admitted S K).2 f).mpr h

theorem freeCase {S K m n σ x} : TermAt S K m (n+1) (.free σ x) := by
  intro h hm _
  exact freeMem (h.1 σ (subtypeSelf σ)) hm

theorem boundCase {S K m n σ i} : TermAt S K m (n+1) (.bound σ i) := by
  intro h hm _
  exact boundMem (h.1 σ (subtypeSelf σ)) hm

theorem bottomCase {S K m n σ} : TermAt S K m (n+1) (.bottom σ) := by
  intro h _ _
  exact bottomMem (h.1 σ (subtypeSelf σ))

theorem lamCase {S K m n σ Q} (iq : TermAt S K m n Q) :
    TermAt S K m (n+1) (.lam σ Q) := by
  intro h hm hn
  have hσ := h.1 σ (List.mem_append_left _ (List.mem_append_right _ (subtypeSelf σ)))
  have hq : TermGuard S K Q := ⟨fun t hp => h.1 t (List.mem_append_right _ hp),h.2⟩
  simp only [termBounds] at hn
  exact lamMem hσ (iq hq hm (by omega))

theorem ordinaryCase {S K m n f qs} (ia : ArgsAt S K m n qs) :
    TermAt S K m (n+1) (.ordinary f qs) := by
  intro h hm hn
  have hf := admittedMem (h.2 f List.mem_cons_self)
  have hqs : ArgsGuard S K qs :=
    ⟨fun t ht => h.1 t (List.mem_append_right _ ht),
      fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩
  simp only [termBounds] at hn
  exact ordinaryMem hf (ia hqs hm (by omega))

theorem argsConsCase {S K m n Q qs} (iq : TermAt S K m n Q) (ia : ArgsAt S K m n qs) :
    ArgsAt S K m (n+1) (.cons Q qs) := by
  intro h hm hn
  obtain ⟨hq,ha⟩ := consParts h
  simp only [argsBounds] at hm hn
  exact consMem (iq hq (Nat.le_trans (Nat.le_max_left _ _) hm) (by omega))
    (ia ha (Nat.le_trans (Nat.le_max_right _ _) hm) (by omega))

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSimpleProof
