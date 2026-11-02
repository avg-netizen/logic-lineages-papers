module
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusStructureProof
public import LogicLineages.OrdinalComparison.SourceUnaryChainAlgebraProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
open AdmissibleSum SourceUnaryChain.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem three_value {Γ} (p : Policy) (site : MacroSite) (a b c : OrdinalExpression Γ)
    (ν : OrdinalComponent Γ → Ordinal) :
    denote ν (AdmissiblePartial.three p site a b c) =
      ordinalNaturalSum (ordinalNaturalSum (denote ν a) (denote ν b)) (denote ν c) := by
  have he := actualAdmissibleSumValue Γ 3 (p.shape site 2) (.join (.join .leaf .leaf) .leaf)
    (fun i : Fin 3 => if i.val = 0 then a else if i.val = 1 then b else c) ν
  simpa [AdmissiblePartial.three, expand, denote] using he

theorem finite_surplus_add (a b : Ordinal) (m n : Nat) :
    ordinalNaturalSum (ordinalNaturalSum (a + (m : Ordinal)) (b + (n : Ordinal))) 1 =
      ordinalNaturalSum a b + ((m + n + 1 : Nat) : Ordinal) := by
  rw [← actualNaturalSumFiniteRight a m, ← actualNaturalSumFiniteRight b n]
  have hshuffle : ordinalNaturalSum (ordinalNaturalSum a (m : Ordinal))
      (ordinalNaturalSum b (n : Ordinal)) =
      ordinalNaturalSum (ordinalNaturalSum a b) (ordinalNaturalSum (m : Ordinal) (n : Ordinal)) := by
    rw [sum_assoc a (m : Ordinal), ← sum_assoc (m : Ordinal) b,
      sum_comm (m : Ordinal) b, sum_assoc b (m : Ordinal), ← sum_assoc a b]
  rw [hshuffle, naturalSum_finite, sum_assoc, show (1 : Ordinal) = ((1 : Nat) : Ordinal) from by simp,
    naturalSum_finite, actualNaturalSumFiniteRight]

theorem finite_count_add (m n : Nat) :
    ordinalNaturalSum (ordinalNaturalSum (m : Ordinal) (n : Ordinal)) 1 =
      ((m + n + 1 : Nat) : Ordinal) := by
  rw [naturalSum_finite]
  simpa using naturalSum_finite (m+n) 1

end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
