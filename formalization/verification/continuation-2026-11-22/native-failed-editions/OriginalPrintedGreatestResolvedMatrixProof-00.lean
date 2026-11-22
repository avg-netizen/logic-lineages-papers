module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixGateProof
import LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolutionProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
open OriginalPrintedGreatestGateResolution (Mode exactUniformOriginalResolvedBranch)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue allAppend splitActual)

private theorem appendActual (f θ : Nat → Nat) (rs ss : List Row) (xs ys : Snapshot)
    (hx : actualRows f θ rs xs) (hy : actualRows f θ ss ys) :
    actualRows f θ (rs ++ ss) (xs ++ ys) := by
  induction rs generalizing xs with
  | nil =>
      cases xs with
      | nil => exact hy
      | cons x xs => exact False.elim hx
  | cons r rs ih =>
      cases xs with
      | nil => exact False.elim hx
      | cons x xs => exact ⟨hx.1,hx.2.1,hx.2.2.1,ih xs hx.2.2.2⟩

private theorem positiveAppend (f θ : Nat → Nat) (rs ss : List Row) :
    PositiveRows f θ (rs ++ ss) ↔ PositiveRows f θ rs ∧ PositiveRows f θ ss := by
  constructor
  · rintro ⟨snap,live,yes⟩
    obtain ⟨xs,ys,eq,hx,hy⟩ := splitActual f θ rs ss snap live
    rw [eq] at yes
    obtain ⟨tx,ty⟩ := (allAppend xs ys).mp yes
    exact ⟨⟨xs,hx,tx⟩,⟨ys,hy,ty⟩⟩
  · rintro ⟨⟨xs,hx,tx⟩,⟨ys,hy,ty⟩⟩
    exact ⟨xs ++ ys,appendActual f θ rs ss xs ys hx hy,(allAppend xs ys).mpr ⟨tx,ty⟩⟩

private theorem emitted (f θ : Nat → Nat) (ms : List Mode) :
    PositiveRows f θ (ms.flatMap emit) ↔ ∀ m ∈ ms, m.Holds f θ := by
  induction ms with
  | nil => simp [PositiveRows,actualRows,AllTrue]
  | cons m ms ih =>
      change PositiveRows f θ (emit m ++ ms.flatMap emit) ↔ _
      rw [positiveAppend,exactModeMatrix f θ m,ih]
      constructor
      · rintro ⟨head,tail⟩ n hn
        rcases List.mem_cons.mp hn with eq | rest
        · exact eq.symm ▸ head
        · exact tail n rest
      · intro h
        exact ⟨h m List.mem_cons_self,fun n hn => h n (List.mem_cons_of_mem _ hn)⟩

theorem exactUniformResolvedMatrix : ExactUniformResolvedMatrix := by
  intro f B hf θ known gates p plain branch member ordered z paid prior positive ν
  have resolved := exactUniformOriginalResolvedBranch f B hf θ known gates p branch
    member ordered z paid prior positive
  change (prior ν ∧ OriginalPrintedPlainMatrixOrderBranches.SourceAccepts f ν known gates p positive) ↔
    (prior ν ∧ PacketAccepts f ν (prefixRows known gates p branch) p positive)
  apply resolved.trans
  exact and_congr Iff.rfl
    (and_congr (emitted f ν _).symm (OriginalPlainTerminalMatrix.exactPlainTerminalSuffix f ν p plain positive))

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
