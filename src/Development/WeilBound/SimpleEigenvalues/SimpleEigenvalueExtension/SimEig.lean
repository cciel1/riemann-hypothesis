module

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Order.Minimal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

/-- A commuting family has a common eigenvector in every nonzero finite-dimensional invariant
subspace. -/
theorem exists_common_eigenvector_mem {K V ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] (T : ι → V →ₗ[K] V)
    (hT : ∀ i j v, T i (T j v) = T j (T i v)) (W : Submodule K V) [FiniteDimensional K W] (hW : W ≠ ⊥)
    (hs : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ l : K, T i v = l • v := by
  let P (U : Submodule K V) := U ≤ W ∧ U ≠ ⊥ ∧ ∀ i, ∀ v ∈ U, T i v ∈ U
  obtain ⟨U, hmin⟩ := exists_minimalFor_of_wellFoundedLT P (Module.finrank K ·)
    ⟨W, le_rfl, hW, hs⟩
  obtain ⟨hUW, hU, hstable⟩ := hmin.prop
  have := Submodule.finiteDimensional_of_le hUW
  have := Submodule.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  refine ⟨v, hUW hv, hv0, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hstable i))
  have hinv : P (U ⊓ Module.End.eigenspace (T i) c) := by
    refine ⟨inf_le_left.trans hUW, ?_, fun j x hx => ⟨hstable j x hx.1, ?_⟩⟩
    · exact fun h => hc (Module.End.eigenspace_restrict_eq_bot (hstable i) (disjoint_iff.mpr h).symm)
    · exact Module.End.mapsTo_genEigenspace_of_comm (LinearMap.ext (hT i j)) c 1 hx.2
  have heq : U ⊓ Module.End.eigenspace (T i) c = U :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (hmin.le hinv)
  exact ⟨c, Module.End.mem_eigenspace_iff.mp ((inf_eq_left.mp heq) hv)⟩

end GlobalTheory

theorem UpperTheory.V.LinAlg.simEig :
    ∀ {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
        {J : Type} (T : J → Module.End K M), (∀ i j : J, T i * T j = T j * T i) →
        ∀ (d : ℕ) (U : Submodule K M), Module.finrank K U = d → U ≠ ⊥ → (∀ j : J, ∀ x ∈ U, T j x ∈ U) →
        ∃ v ∈ U, v ≠ 0 ∧ ∀ j : J, ∃ c : K, T j v = c • v := by
  intro K M _ _ _ _ _ J T hT _ U _ hU hst
  exact GlobalTheory.exists_common_eigenvector_mem T (fun i j => LinearMap.congr_fun (hT i j))
    U hU hst
