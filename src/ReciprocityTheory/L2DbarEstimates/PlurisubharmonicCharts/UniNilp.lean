module

import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TracePowEqZeroOfLeDim
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.TypeStar
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

/-- If the first `r` power traces vanish, Cayley–Hamilton gives `N ^ r = 0`. -/
theorem isNilpotent_of_trace_pow {K : Type*} [CommRing K] [HasUniqueDiv K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    IsNilpotent N := by
  have he := GroundTheory.Global.charpoly_eq_of_trace_powers N (0 : Matrix (Fin r) (Fin r) K)
    fun k hk hkr => by simpa [zero_pow hk.ne'] using h k hk (by simpa using hkr)
  refine ⟨r, ?_⟩
  simpa only [he, Matrix.charpoly_zero, Fintype.card_fin, map_pow, Polynomial.aeval_X] using
    Matrix.aeval_self_charpoly N

end ReciprocityTheory.L2DbarEstimates.Y
