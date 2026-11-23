module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverLayerProof
open NumberedWindowSyntax NumberedWindowPrimaryCoverSyntax

abbrev terms (H : List Head) (K : List Ty) (m n : Nat) :=
  (grammar H K m n).1

abbrev cells (H : List Head) (K : List Ty) (m n : Nat) :=
  (grammar H K m n).2

private theorem termLayer (H K m n) :
    terms H K m (n + 1) =
      leaves K (List.range (m + 1)) ++ lambdas K (terms H K m n) ++
      ordinaryHeads H (cells H K m n) ++ numberedHeads H K
        (List.range (m + 1)) (cells H K m n) ++ auxiliaryApps K (terms H K m n) := by
  cases e : grammar H K m n
  simp only [terms,cells,grammar,e]

private theorem cellLayer (H K m n) :
    cells H K m (n + 1) = argumentCells (terms H K m n) (cells H K m n) := by
  cases e : grammar H K m n
  simp only [terms,cells,grammar,e]

private theorem numeral {i m : Nat} (h : i ≤ m) : i ∈ List.range (m + 1) :=
  List.mem_range.mpr (Nat.lt_succ_of_le h)

theorem freeMem {H K m n σ x} (hσ : σ ∈ K) (hx : x ≤ m) :
    NTerm.free σ x ∈ terms H K m (n+1) := by
  have hf : NTerm.free σ x ∈ K.flatMap
      (fun σ => (List.range (m+1)).map (NTerm.free σ)) :=
    List.mem_flatMap.mpr ⟨σ,hσ,List.mem_map_of_mem (numeral hx)⟩
  have hLeaf : NTerm.free σ x ∈ leaves K (List.range (m+1)) :=
    List.mem_append_left _ (List.mem_append_left _ hf)
  simp only [termLayer,List.mem_append,hLeaf,true_or]

theorem boundMem {H K m n σ i} (hσ : σ ∈ K) (hi : i ≤ m) :
    NTerm.bound σ i ∈ terms H K m (n+1) := by
  have hf : NTerm.bound σ i ∈ K.flatMap
      (fun σ => (List.range (m+1)).map (NTerm.bound σ)) :=
    List.mem_flatMap.mpr ⟨σ,hσ,List.mem_map_of_mem (numeral hi)⟩
  have hLeaf : NTerm.bound σ i ∈ leaves K (List.range (m+1)) :=
    List.mem_append_left _ (List.mem_append_right _ hf)
  simp only [termLayer,List.mem_append,hLeaf,true_or]

theorem bottomMem {H K m n σ} (hσ : σ ∈ K) :
    NTerm.bottom σ ∈ terms H K m (n+1) := by
  have hLeaf : NTerm.bottom σ ∈ leaves K (List.range (m+1)) :=
    List.mem_append_right _ (List.mem_map_of_mem hσ)
  simp only [termLayer,List.mem_append,hLeaf,true_or]

theorem lamMem {H K m n σ Q} (hσ : σ ∈ K) (hq : Q ∈ terms H K m n) :
    NTerm.lam σ Q ∈ terms H K m (n+1) := by
  have h : NTerm.lam σ Q ∈ lambdas K (terms H K m n) :=
    List.mem_flatMap.mpr ⟨σ,hσ,List.mem_map_of_mem hq⟩
  simp only [termLayer,List.mem_append,h,true_or,or_true]

theorem ordinaryMem {H K m n f bs} (hf : f ∈ H) (hb : bs ∈ cells H K m n) :
    NTerm.ordinary f bs ∈ terms H K m (n+1) := by
  have h : NTerm.ordinary f bs ∈ ordinaryHeads H (cells H K m n) :=
    List.mem_flatMap.mpr ⟨f,hf,List.mem_map_of_mem hb⟩
  simp only [termLayer,List.mem_append,h,true_or,or_true]

theorem numberedMem {H K m n f τ k bs es} (hf : f ∈ H) (hτ : τ ∈ K)
    (hk : k ≤ m) (hb : bs ∈ cells H K m n) (he : es ∈ cells H K m n) :
    NTerm.numbered f τ k bs es ∈ terms H K m (n+1) := by
  have h : NTerm.numbered f τ k bs es ∈ numberedHeads H K
      (List.range (m+1)) (cells H K m n) :=
    List.mem_flatMap.mpr ⟨f,hf,List.mem_flatMap.mpr ⟨τ,hτ,List.mem_flatMap.mpr
      ⟨k,numeral hk,List.mem_flatMap.mpr ⟨bs,hb,List.mem_map_of_mem he⟩⟩⟩⟩
  simp only [termLayer,List.mem_append,h,true_or,or_true]

theorem auxMem {H K m n σ τ Q A} (hσ : σ ∈ K) (hτ : τ ∈ K)
    (hq : Q ∈ terms H K m n) (ha : A ∈ terms H K m n) :
    NTerm.auxApp σ τ Q A ∈ terms H K m (n+1) := by
  have h : NTerm.auxApp σ τ Q A ∈ auxiliaryApps K (terms H K m n) :=
    List.mem_flatMap.mpr ⟨σ,hσ,List.mem_flatMap.mpr
      ⟨τ,hτ,List.mem_flatMap.mpr ⟨Q,hq,List.mem_map_of_mem ha⟩⟩⟩
  simp only [termLayer,List.mem_append,h,or_true]

theorem nilMem (H K m n) : NArgs.nil ∈ cells H K m n := by
  cases n with
  | zero => exact List.mem_cons_self
  | succ n =>
    rw [cellLayer]
    exact List.mem_cons_self

theorem consMem {H K m n Q qs} (hq : Q ∈ terms H K m n) (hs : qs ∈ cells H K m n) :
    NArgs.cons Q qs ∈ cells H K m (n+1) := by
  rw [cellLayer]
  exact List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨Q,hq,List.mem_map_of_mem hs⟩)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverLayerProof
