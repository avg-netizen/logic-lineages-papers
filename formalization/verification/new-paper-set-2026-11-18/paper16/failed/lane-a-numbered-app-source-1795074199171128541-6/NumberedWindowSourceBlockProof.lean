import LogicLineages.PersistentMarking.NumberedWindowSourceInventoryProof
import LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof

namespace LogicLineages.PersistentMarking.NumberedWindowSourceBlockProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionSourceUniverse
open NumberedWindowDomain NumberedWindowSourceGuardTargets NumberedWindowSourceInventoryProof

theorem term : ActualBlockGuard := by
  intro S K C types values q σ hQ hV
  let V := freeInventory q ++ freeInventoryArgs values
  let H := heads q ++ headsArgs values
  have hu : Universe K V H [] q :=
    ⟨hQ.2.2,fun f hf => List.mem_append_left _ hf,
      fun n hn => Or.inl (List.mem_append_left _ ((DecisionInventoryProof.freeExact q n).mp hn))⟩
  have hv : ArgsUniverse K V H [] values := supportArgs K V H [] values hV.2.2
    (fun f hf => List.mem_append_right _ hf) (fun n hn => Or.inl (List.mem_append_right _ hn))
  have hc := SpineSubstitutionProof.finiteCompatible C values types hV.1
  have result := DecisionSourceSubstitutionProof.preserves K V H [] (BoundContext.prefix types C) C
    values 0 q σ hc hQ.1 hu hv
  refine ⟨SpineSubstitutionProof.parallelPreserves C types values q σ hV.1 hQ.1,?_,result.1⟩
  apply validOfHeads
  intro f hf
  have h : f ∈ heads q ++ headsArgs values := result.2.1 f hf
  rcases List.mem_append.mp h with ht | ht
  · exact NumberedWindowRealizationWindowProof.admitted S q hQ.2.1 f ht
  · exact validArgsHeads S values hV.2.1 f ht

theorem base (S : Signature) (K : List Ty) (C : BoundContext) (types : List Ty)
    (values bs : Spine.Args) (bTypes : List Ty)
    (hB : SourceValues S K (BoundContext.prefix types C) bTypes bs)
    (hV : SourceValues S K C types values) :
    SourceValues S K C bTypes (Spine.substituteArgs values 0 bs) := by
  cases bs with
  | nil =>
    cases hB.1
    exact ⟨.nil,True.intro,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons q xs =>
    cases hB.1 with
    | cons hq hxs =>
      have hQ := term S K C types values q _
        ⟨hq,hB.2.1.1,fun ρ hρ => hB.2.2 ρ (List.mem_append_left _ hρ)⟩ hV
      have hTail := base S K C types values xs _
        ⟨hxs,hB.2.1.2,fun ρ hρ => hB.2.2 ρ (List.mem_append_right _ hρ)⟩ hV
      refine ⟨.cons hQ.1 hTail.1,⟨hQ.2.1,hTail.2.1⟩,?_⟩
      intro ρ hρ
      simp only [Spine.substituteArgs,auxiliaryArgs,List.mem_append] at hρ
      exact hρ.elim (hQ.2.2 ρ) (hTail.2.2 ρ)
termination_by sizeOf bs

theorem extras (S : Signature) (K : List Ty) (C : BoundContext) (types : List Ty)
    (values es : Spine.Args)
    (hE : Spine.ExtrasTyped (BoundContext.prefix types C) es)
    (hValid : ValidArgs S es) (hSupport : SymbolicArgsAdmissible K es)
    (hV : SourceValues S K C types values) :
    Spine.ExtrasTyped C (Spine.substituteArgs values 0 es) ∧
      ValidArgs S (Spine.substituteArgs values 0 es) ∧
      SymbolicArgsAdmissible K (Spine.substituteArgs values 0 es) := by
  cases es with
  | nil => exact ⟨.nil,True.intro,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons q xs =>
    cases hE with
    | cons hq hxs =>
      have hQ := term S K C types values q _
        ⟨hq,hValid.1,fun ρ hρ => hSupport ρ (List.mem_append_left _ hρ)⟩ hV
      have hTail := extras S K C types values xs hxs hValid.2
        (fun ρ hρ => hSupport ρ (List.mem_append_right _ hρ)) hV
      refine ⟨.cons hQ.1 hTail.1,⟨hQ.2.1,hTail.2.1⟩,?_⟩
      intro ρ hρ
      simp only [Spine.substituteArgs,auxiliaryArgs,List.mem_append] at hρ
      exact hρ.elim (hQ.2.2 ρ) (hTail.2.2 ρ)
termination_by sizeOf es

end LogicLineages.PersistentMarking.NumberedWindowSourceBlockProof
