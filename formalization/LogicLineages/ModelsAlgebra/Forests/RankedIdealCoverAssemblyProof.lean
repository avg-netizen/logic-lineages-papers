module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssemblyTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCodeStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssembly.Proof
open RankedParse RankedIdealRegularCode RankedIdealSpineCode RankedIdealComponents
open RankedIdealCompletion RankedGraphImage RankedIdealConstructors RankedIdealSpine

private theorem outputExact (C : Code) (q : C.machine.State) B t :
    language (linearList B (frames C q)) t ↔ linearPiece (alphabet C q) (language B) t := by
  exact RankedIdealRegularCode.StatementChecks.linearExact B (frames C q).length
    (fun i => (frames C q)[i]) t

theorem piecesIdeal : Targets.PiecesIdeal := by
  intro C q rec h B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact RankedIdealRegularCode.StatementChecks.linearIdeal A (frames C q).length
    (fun i => (frames C q)[i]) (RankedIdealSpineCode.StatementChecks.seedsIdeal C q rec h A hA)

private theorem seedWitness (C : Code) (q : C.machine.State) rec (h : LowerCorrect C q rec)
    t (ht : Star (Frame C.machine q) (Entry C.machine q) t) :
    ∃ B ∈ seeds C q rec, Star (alphabet C q) (language B) t := by
  induction ht with
  | base ht =>
      obtain ⟨B, hB, hb⟩ := RankedIdealSpineCode.StatementChecks.entriesCovered C q rec h _ ht
      exact ⟨B, hB, .base hb⟩
  | step hc _ ih =>
      obtain ⟨B, hB, hb⟩ := ih
      exact ⟨B, hB, .step ((RankedIdealSpineCode.StatementChecks.framesExact C q _).mpr hc) hb⟩

theorem piecesExact : Targets.PiecesExact := by
  intro C q rec h hn t
  constructor
  · rintro ⟨B, hB, ht⟩
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    obtain ⟨u, hu, htu⟩ := (outputExact C q A t).mp ht
    have hr : Run C.machine u q := by
      clear htu
      induction hu with
      | base ha => exact RankedIdealSpineCode.StatementChecks.seedsSound C q rec h A hA _ ha
      | step hc _ ih =>
          exact RankedIdealSpine.StatementChecks.frameSound C.machine q _ _
            ((RankedIdealSpineCode.StatementChecks.framesExact C q _).mp hc) ih
    exact RankedIdealComponents.StatementChecks.stateLanguageDownward C.machine q t u htu hr
  · intro ht
    have hs := (RankedIdealSpine.StatementChecks.linearSpineExact C.machine q hn t).mp ht
    obtain ⟨B, hB, hb⟩ := seedWitness C q rec h t hs
    refine ⟨linearList B (frames C q), List.mem_map.mpr ⟨B, hB, rfl⟩, ?_⟩
    exact (outputExact C q B t).mpr ⟨t, hb, RankedIdealContext.StatementChecks.embeddingReflexive t⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssembly.Proof
