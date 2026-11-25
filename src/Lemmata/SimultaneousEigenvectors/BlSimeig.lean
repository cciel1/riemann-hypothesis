module

import Development.WeilBound.SimpleEigenvalues.SimpleEigenvalueExtension.SimEig
import Mathlib.Analysis.Complex.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

universe u_1

namespace Bl.SimultaneousEigenvectors

private theorem diagonal_commute {n : ℕ} {X : Type u_1} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : ReciprocityTheory.ChartRestriction.DS.IsGlRep A)
    (c d : Fin n) : Commute (A c c) (A d d) := by
  by_cases hcd : c = d
  · subst d; exact Commute.refl _
  · exact sub_eq_zero.mp (by simpa only [ite_eq_right hcd, ite_eq_right (Ne.symm hcd), sub_zero] using hA c c d d)

theorem goal1 {n : ℕ} {X : Type u_1} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {A : Fin n → Fin n → Module.End ℂ X} (hA : ReciprocityTheory.ChartRestriction.DS.IsGlRep A)
    (s : Finset (Fin n)) :
    ∀ (T : Submodule ℂ X), FiniteDimensional ℂ T → (∀ (c : Fin n) (v : X), v ∈ T → A c c v ∈ T) →
      T ≠ ⊥ → ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  intro T _ hinv hne
  obtain ⟨w, hw, hw0, h⟩ := GlobalTheory.exists_common_eigenvector_mem (fun i => A i i)
    (fun i j => LinearMap.congr_fun (diagonal_commute hA i j).eq) T hne hinv
  choose μ hμ using h
  exact ⟨w, hw, hw0, μ, fun i _ => hμ i⟩

end Bl.SimultaneousEigenvectors
