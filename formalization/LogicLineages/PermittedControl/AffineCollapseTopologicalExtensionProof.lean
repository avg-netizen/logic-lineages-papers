module
public import LogicLineages.PermittedControl.AffineCollapseTopologicalExtensionTargets
import LogicLineages.PermittedControl.AffineCollapseTopologicalExtensionLocalityProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseTopologicalExtension
open OrdinalComparison
open AffineCollapsePairListLow (Pair GraphsAt)

private theorem graphsCons (f : Nat → Nat) (p : Pair) (ps : List Pair) (θ : Valuation) :
    GraphsAt f θ (p :: ps) ↔ graphAt f p θ ∧ GraphsAt f θ ps := by
  constructor
  · intro h
    exact ⟨h p List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
  · rintro ⟨h,pTail⟩ q hq
    rcases List.mem_cons.mp hq with he | ht
    · subst q
      exact h
    · exact pTail q ht

theorem exactTopologicalExtension : ExactTopologicalExtension := by
  intro f B sel known pairs
  induction pairs generalizing known with
  | nil =>
      intro _ base final
      constructor
      · intro h
        have eq : base = final := Option.some.inj h
        subst final
        exact ⟨by simp [GraphsAt],fun _ _ => rfl⟩
      · rintro ⟨_,outside⟩
        apply congrArg some
        funext n
        exact (outside n (by simp [born])).symm
  | cons p ps ih =>
      intro top base final
      let seen := input p :: output p :: known
      have tailTop : Topological seen ps := top.2.2.2.2
      let next := put p base (valuesAt f p base)
      have tailExact := ih seen tailTop next final
      constructor
      · intro h
        classical
        by_cases paid : domainAt p base
        · have tailRun : run f next ps = some final := by
            simpa only [run,if_pos paid,next] using h
          obtain ⟨tailGraph,tailAgree⟩ := tailExact.mp tailRun
          have head : graphAt f p next := (headExact f B sel known p ps top base _).mpr ⟨paid,rfl⟩
          have finalHead := (headGraphOfTailAgreement f known p ps top next final tailAgree).mpr head
          exact ⟨(graphsCons f p ps final).mpr ⟨finalHead,tailGraph⟩,
            restrictTailAgreement p ps base final _ tailAgree⟩
        · simp only [run,if_neg paid] at h
          cases h
      · rintro ⟨graphs,outside⟩
        obtain ⟨head,tailGraph⟩ := (graphsCons f p ps final).mp graphs
        let vals := (final (input p),final (output p))
        have tailAgree : AgreesOutside ps (put p base vals) final :=
          extendTailAgreement p ps base final top.1 outside
        have headMiddle := (headGraphOfTailAgreement f known p ps top _ final tailAgree).mp head
        obtain ⟨paid,eq⟩ := (headExact f B sel known p ps top base vals).mp headMiddle
        rw [eq] at tailAgree
        have tailRun := tailExact.mpr ⟨tailGraph,tailAgree⟩
        classical
        simpa only [run,if_pos paid,next] using tailRun

theorem uniqueTopologicalExtension : UniqueTopologicalExtension := by
  intro f B sel known pairs top base
  have result := exactTopologicalExtension f B sel known pairs top base
  constructor
  · constructor
    · intro success
      cases hR : run f base pairs with
      | none => exact (success hR).elim
      | some final =>
          refine ⟨final,(result final).mp hR,?_⟩
          intro other prop
          exact Option.some.inj (((result other).mpr prop).symm.trans hR)
    · rintro ⟨final,actual,_⟩
      have yes := (result final).mpr actual
      intro no
      rw [no] at yes
      cases yes
  · intro final good n hn
    exact ((result final).mp good).2 n (knownNotBorn known pairs top n hn)

end LogicLineages.PermittedControl.AffineCollapseTopologicalExtension
