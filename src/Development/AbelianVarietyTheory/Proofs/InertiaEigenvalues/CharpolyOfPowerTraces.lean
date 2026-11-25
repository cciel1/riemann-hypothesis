module

import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace GlobalTheory.CharpolyNewton

open Polynomial Finset

private lemma exists_fin_family {R : Type*} (s : Multiset R) {a : ℕ} (ha : s.card = a) :
    ∃ b : Fin a → R, s = Finset.univ.val.map b := by
  have hs : s = Finset.univ.val.map s.toList.get := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  exact (s.length_toList.trans ha) ▸ ⟨s.toList.get, hs⟩

/-- A size-`a` matrix has the prescribed characteristic polynomial when its first `a` power
traces agree with the power sums of the proposed roots, counted with multiplicity. -/
theorem charpoly_eq_prod_of_trace_pow (k : Type) [CommRing k] [HasUniqueDiv k]
    (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (B : Multiset k) (hB : B.card = a)
    (h : ∀ n : Fin (a + 1), 1 ≤ (n : ℕ) → (M ^ (n : ℕ)).trace = (B.map (· ^ (n : ℕ))).sum) :
    M.charpoly = (B.map fun b => X - C b).prod := by
  classical
  obtain ⟨b, rfl⟩ := exists_fin_family B hB
  rw [Multiset.map_map, ← Finset.prod, Function.comp_def, ← Matrix.charpoly_diagonal]
  apply GroundTheory.Global.charpoly_eq_of_trace_powers
  intro j hj hja
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  simpa only [Multiset.map_map, Finset.sum, Function.comp_def, Pi.pow_apply] using h ⟨j, by simpa using hja⟩ hj

/-- Equal-cardinality multisets with equal power sums give the same split monic polynomial. -/
theorem prod_eq_of_psum_eq {k : Type} [CommRing k] [HasUniqueDiv k] (s t : Multiset k)
    (hc : s.card = t.card) (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    (s.map (fun b => X - C b)).prod = (t.map (fun b => X - C b)).prod := by
  classical
  obtain ⟨b, rfl⟩ := exists_fin_family s hc
  have he := charpoly_eq_prod_of_trace_pow k t.card (Matrix.diagonal b) t rfl (fun n _ => by
    simpa only [Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply, Finset.sum,
      Multiset.map_map, Function.comp_def] using h n)
  simpa only [Matrix.charpoly_diagonal, Finset.prod, Multiset.map_map, Function.comp_def] using he

end GlobalTheory.CharpolyNewton
