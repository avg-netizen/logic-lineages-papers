module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCodeTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode.Proof
open RankedParse ProfileAutomatonEncoding ProfileSourceRegular RankedIdealRegularCode
open RankedGraphImage ForestParseRepresentation

theorem sourceCodeExact : Targets.SourceCodeExact := by
  intro F t
  exact ProfileSourceRegular.StatementChecks.sourceMachineCorrect F t

theorem sourceCoverIdeals : Targets.SourceCoverIdeals := by
  intro F B hB
  exact (RankedIdealCover.StatementChecks.coverCorrect (sourceCode F)).1 B hB

theorem sourceCoverExact : Targets.SourceCoverExact := by
  intro F t
  constructor
  · intro ht
    apply ((RankedIdealCover.StatementChecks.coverCorrect (sourceCode F)).2 t).mpr
    exact ⟨t, (sourceCodeExact F t).mpr ht, RankedIdealContext.StatementChecks.embeddingReflexive t⟩
  · intro ht
    obtain ⟨u, hu, htu⟩ := ((RankedIdealCover.StatementChecks.coverCorrect (sourceCode F)).2 t).mp ht
    exact (ProfileSourceRegular.StatementChecks.generalForbiddenRegular (F.map rawFinite)).2
      t u htu ((sourceCodeExact F u).mp hu)

theorem sourceCoverEmpty : Targets.SourceCoverEmpty := by
  intro F
  change RankedIdealCover.cover (sourceCode F) = [] ↔ _
  rw [RankedIdealCover.StatementChecks.emptyExact (sourceCode F)]
  constructor
  · intro h t ht
    exact h t ((sourceCodeExact F t).mpr ht)
  · intro h t ht
    exact h t ((sourceCodeExact F t).mp ht)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode.Proof
