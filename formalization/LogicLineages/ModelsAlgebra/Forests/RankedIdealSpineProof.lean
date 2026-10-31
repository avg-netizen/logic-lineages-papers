module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRankStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealCompletion RankedIdealComponents RankedIdealConstructors RankedIdealFinite RankedIdealRank RankedIdealContext
open RankedIdealComponents.StatementChecks
 theorem entrySound : Targets.EntrySound := by
  intro M _ q t h
  cases h with
  | atom hc => exact reachLanguageInclusion M _ q hc.2 _ .atom
  | lower hl hr => exact reachLanguageInclusion M _ q hl.1 _ hr
  | node hx hy hc px py hl hr =>
      exact reachLanguageInclusion M _ q hc.2 _ (.node _ hl hr px py)
 theorem frameSound : Targets.FrameSound := by
  intro M _ q c t hc ht
  cases hc with
  | left hx hy ho px py hr =>
      exact reachLanguageInclusion M _ q ho.2 _
        (.node _ (reachLanguageInclusion M q _ hx.1 _ ht) hr px py)
  | right hx hy ho px py hl =>
      exact reachLanguageInclusion M _ q ho.2 _
        (.node _ hl (reachLanguageInclusion M q _ hy.1 _ ht) px py)
 theorem linearSpineExact : Targets.LinearSpineExact := by
  intro M _ q hn t
  constructor
  · intro ht
    have aux : ∀ u p, Run M u p → SameComponent M q p →
        Star (Frame M q) (Entry M q) u := by
      intro u p h
      induction h with
      | atom => intro hc; exact .base (.atom hc)
      | node o hl hr px py ihl ihr =>
          intro hc
          rcases RankedIdealRank.StatementChecks.linearChildren M q o _ _ hn px py hc with
            ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact .base (.node hx hy hc px py hl hr)
          · exact .step (.left hx hy hc px py hr) (ihl hx)
          · exact .step (.right hx hy hc px py hl) (ihr hy)
      | @epsilon u x y hr he ih =>
          intro hc
          have hxy : y ∈ close M {x} :=
            (RankedIdealFinite.StatementChecks.closureExact M {x} y).mpr
              (.edge (.seed (by simp)) he)
          have hxq := RankedIdealRank.StatementChecks.reachTransitive M x y q hxy hc.2
          rcases RankedIdealRank.StatementChecks.predecessorCases M x q hxq with hs | hl
          · exact ih ⟨hs.2, hs.1⟩
          · exact .base (.lower hl hr)
    exact aux t q ht ⟨RankedIdealRank.StatementChecks.reachReflexive M q,
      RankedIdealRank.StatementChecks.reachReflexive M q⟩
  · intro ht
    induction ht with
    | base h => exact entrySound M q _ h
    | step hc _ ih => exact frameSound M q _ _ hc ih
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine.Proof
